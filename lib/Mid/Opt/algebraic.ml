(* ToyC 优化 — 代数化简
   x+0→x, x*1→x, x*0→0, x-x→0, x/x→1 等 *)

open Ir_types
open Common

module IntMap = Map.Make (Int)

let rec resolve_value (repl : value IntMap.t) (v : value) : value =
  match v with
  | VReg r ->
    (match IntMap.find_opt r repl with
     | Some v' -> resolve_value repl v'
     | None -> v)
  | Imm _ | Global _ -> v

let apply_repl (f : func) (repl : value IntMap.t) : func =
  let rv = resolve_value repl in
  let ri instr = match instr with
    | Alloca _ -> instr
    | Load l   -> Load { l with ptr = rv l.ptr }
    | Store s  -> Store { val_ = rv s.val_; ptr = rv s.ptr }
    | Binop b  -> Binop { b with lhs = rv b.lhs; rhs = rv b.rhs }
    | Icmp c   -> Icmp { c with lhs = rv c.lhs; rhs = rv c.rhs }
    | Call c   -> Call { c with args = List.map rv c.args }
    | Phi p    -> Phi { p with incoming = List.map (fun (v, l) -> (rv v, l)) p.incoming }
    | Shl s    -> Shl { s with lhs = rv s.lhs; rhs = rv s.rhs }
    | AShr s   -> AShr { s with lhs = rv s.lhs; rhs = rv s.rhs }
    | And a    -> And { a with lhs = rv a.lhs; rhs = rv a.rhs }
    | Zext z   -> Zext { z with src = rv z.src }
    | Copy c   -> Copy { c with src = rv c.src }
  in
  let rt = function
    | Ret (Some v)    -> Ret (Some (rv v))
    | Ret None        -> Ret None
    | Br (cond, t, f) -> Br (rv cond, t, f)
    | Jump _ as j     -> j
  in
  let new_blocks = List.map (fun (lbl, bb) ->
    let new_instrs = List.filter_map (fun instr ->
      match instr_dst instr with
      | Some dst when IntMap.mem dst repl -> None
      | _ -> Some (ri instr)
    ) bb.bb_instrs in
    (lbl, { bb with bb_instrs = new_instrs; bb_term = rt bb.bb_term })
  ) f.f_blocks in
  { f with f_blocks = new_blocks }

let simplify_binop op lhs rhs : value option =
  match op, lhs, rhs with
  | Add, x, Imm 0
  | Add, Imm 0, x ->
      Some x
  | Sub, x, Imm 0 ->
      Some x
  | Sub, VReg x, VReg y when x = y ->
      Some (Imm 0)
  | Mul, _, Imm 0
  | Mul, Imm 0, _ ->
      Some (Imm 0)
  | Mul, x, Imm 1
  | Mul, Imm 1, x ->
      Some x
  | Div, x, Imm 1 ->
      Some x
  | Mod, _, Imm 1 ->
      Some (Imm 0)
  | Eq, VReg x, VReg y when x = y ->
      Some (Imm 1)
  | Ne, VReg x, VReg y when x = y ->
      Some (Imm 0)
  | Lt, VReg x, VReg y when x = y ->
      Some (Imm 0)
  | Gt, VReg x, VReg y when x = y ->
      Some (Imm 0)
  | Le, VReg x, VReg y when x = y ->
      Some (Imm 1)
  | Ge, VReg x, VReg y when x = y ->
      Some (Imm 1)
  | _ ->
      None

let simplify_icmp cond lhs rhs : value option =
  match cond, lhs, rhs with
  | IEq, VReg x, VReg y when x = y ->
      Some (Imm 1)
  | INe, VReg x, VReg y when x = y ->
      Some (Imm 0)
  | ISlt, VReg x, VReg y when x = y ->
      Some (Imm 0)
  | ISgt, VReg x, VReg y when x = y ->
      Some (Imm 0)
  | ISle, VReg x, VReg y when x = y ->
      Some (Imm 1)
  | ISge, VReg x, VReg y when x = y ->
      Some (Imm 1)
  | _ ->
      None

let run_on_func (f : func) : func =
  let rec fixpoint (f : func) : func =
    let repl = ref IntMap.empty in
    List.iter (fun (_, bb) ->
      List.iter (fun instr ->
        match instr with
        | Binop { dst; op; lhs; rhs } ->
            let lhs = resolve_value !repl lhs in
            let rhs = resolve_value !repl rhs in
            begin match simplify_binop op lhs rhs with
            | Some v -> repl := IntMap.add dst v !repl
            | None -> ()
            end
        | Icmp { dst; cond; lhs; rhs } ->
            let lhs = resolve_value !repl lhs in
            let rhs = resolve_value !repl rhs in
            begin match simplify_icmp cond lhs rhs with
            | Some v -> repl := IntMap.add dst v !repl
            | None -> ()
            end
        | _ -> ()
      ) bb.bb_instrs
    ) f.f_blocks;
    if IntMap.is_empty !repl then f
    else fixpoint (apply_repl f !repl)
  in
  fixpoint f

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
