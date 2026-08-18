(* ToyC 优化 — 公共子表达式消除 (CSE)
   SSA 下扫一遍即可: 相同操作数的相同运算 → 替换为第一个结果 *)

open Ir_types
open Common

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)
type expr_key =
  | KBinop of binary_op * value * value
  | KIcmp of icmp_cond * value * value
  | KZext of value

module ExprMap = Map.Make (struct
  type t = expr_key
  let compare = compare
end)

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

let normalize_commutative a b =
  if compare a b <= 0 then a, b else b, a

let expr_key_of_instr (instr : instr) : ExprMap.key option =
  match instr with
  | Binop { op; lhs; rhs; _ } ->
      begin match op with
      | Add | Mul ->
          let lhs, rhs = normalize_commutative lhs rhs in
          Some (KBinop (op, lhs, rhs))
      | _ ->
          Some (KBinop (op, lhs, rhs))
      end
  | Icmp { cond; lhs; rhs; _ } ->
      begin match cond with
      | IEq | INe ->
          let lhs, rhs = normalize_commutative lhs rhs in
          Some (KIcmp (cond, lhs, rhs))
      | _ ->
          Some (KIcmp (cond, lhs, rhs))
      end
  | Zext { src; _ } ->
      Some (KZext src)
  | _ ->
      None

let rewrite_instr (repl : value IntMap.t) (instr : instr) : instr =
  let rv = resolve_value repl in
  match instr with
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

let run_on_func (f : func) : func =
  let dom = Dominance.analyze f in
  let block_map =
    List.fold_left (fun acc (lbl, bb) -> IntMap.add lbl bb acc) IntMap.empty f.f_blocks
  in
  let repl = ref IntMap.empty in

  let rec dfs lbl (env : int ExprMap.t) =
    let bb = IntMap.find lbl block_map in
    let env_ref = ref env in
    List.iter (fun instr ->
      let instr = rewrite_instr !repl instr in
      match instr_dst instr, expr_key_of_instr instr with
      | Some dst, Some key ->
          begin match ExprMap.find_opt key !env_ref with
          | Some prev ->
              repl := IntMap.add dst (VReg prev) !repl;
              ()
          | None ->
              env_ref := ExprMap.add key dst !env_ref
          end
      | _ ->
          ()
    ) bb.bb_instrs;
    match IntMap.find_opt lbl dom.Dominance.children with
    | Some children -> IntSet.iter (fun child -> dfs child !env_ref) children
    | None -> ()
  in

  dfs f.f_entry ExprMap.empty;
  if IntMap.is_empty !repl then f else apply_repl f !repl

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
