(* ToyC 优化 — 稀疏条件常量传播 (SCCP)
   SSA 格: Top / Bottom(常量) / Overdefined.
   穿越分支传播常量, 比 ConstProp 更强。
   额外识别不可变全局常量的 load。 *)

open Ir_types
open Common

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)
module StringMap = Map.Make (String)

type lattice =
  | Unknown
  | Const of int
  | Overdefined

let join_lattice a b =
  match a, b with
  | Overdefined, _
  | _, Overdefined ->
      Overdefined
  | Unknown, x
  | x, Unknown ->
      x
  | Const x, Const y ->
      if x = y then Const x else Overdefined

let eval_binop_const (op : binary_op) (a : int) (b : int) : int =
  match op with
  | Add -> a + b
  | Sub -> a - b
  | Mul -> a * b
  | Div -> a / b
  | Mod -> a mod b
  | Eq  -> if a = b then 1 else 0
  | Ne  -> if a <> b then 1 else 0
  | Lt  -> if a < b then 1 else 0
  | Gt  -> if a > b then 1 else 0
  | Le  -> if a <= b then 1 else 0
  | Ge  -> if a >= b then 1 else 0
  | LAnd | LOr -> failwith "LAnd/LOr should be lowered before IR"

let eval_icmp_const (cond : icmp_cond) (a : int) (b : int) : int =
  match cond with
  | IEq  -> if a = b then 1 else 0
  | INe  -> if a <> b then 1 else 0
  | ISlt -> if a < b then 1 else 0
  | ISle -> if a <= b then 1 else 0
  | ISgt -> if a > b then 1 else 0
  | ISge -> if a >= b then 1 else 0

let lattice_of_value (state : lattice IntMap.t) = function
  | Imm n -> Const n
  | Global _ -> Overdefined
  | VReg r -> Option.value (IntMap.find_opt r state) ~default:Unknown

let lattice_of_load (global_consts : int StringMap.t) (ptr : value) : lattice =
  match ptr with
  | Global name ->
      begin
        match StringMap.find_opt name global_consts with
        | Some n -> Const n
        | None -> Overdefined
      end
  | _ ->
      Overdefined

let same_value a b =
  match a, b with
  | Imm x, Imm y -> x = y
  | VReg x, VReg y -> x = y
  | Global x, Global y -> x = y
  | _ -> false

let transfer_binop (state : lattice IntMap.t) (op : binary_op) (lhs : value) (rhs : value) : lattice =
  let l = lattice_of_value state lhs in
  let r = lattice_of_value state rhs in
  match l, r with
  | Const a, Const b ->
      Const (eval_binop_const op a b)
  | _, _ when same_value lhs rhs ->
      begin match op with
      | Eq | Le | Ge -> Const 1
      | Ne | Lt | Gt | Sub -> Const 0
      | _ -> Overdefined
      end
  | _, Const 0 when op = Add || op = Sub ->
      l
  | Const 0, _ when op = Add ->
      r
  | _, Const 1 when op = Mul || op = Div ->
      l
  | Const 1, _ when op = Mul ->
      r
  | _, Const 0 when op = Mul ->
      Const 0
  | Const 0, _ when op = Mul ->
      Const 0
  | _, Const 1 when op = Mod ->
      Const 0
  | Overdefined, _
  | _, Overdefined ->
      Overdefined
  | _ ->
      Unknown

let transfer_icmp (state : lattice IntMap.t) (cond : icmp_cond) (lhs : value) (rhs : value) : lattice =
  let l = lattice_of_value state lhs in
  let r = lattice_of_value state rhs in
  match l, r with
  | Const a, Const b ->
      Const (eval_icmp_const cond a b)
  | _, _ when same_value lhs rhs ->
      begin match cond with
      | IEq | ISle | ISge -> Const 1
      | INe | ISlt | ISgt -> Const 0
      end
  | Overdefined, _
  | _, Overdefined ->
      Overdefined
  | _ ->
      Unknown

let transfer_phi (reachable : IntSet.t) (state : lattice IntMap.t) (incoming : (value * label) list) : lattice =
  List.fold_left (fun acc (v, pred) ->
    if not (IntSet.mem pred reachable) then acc
    else
      let lv = lattice_of_value state v in
      match acc with
      | None -> Some lv
      | Some cur -> Some (join_lattice cur lv)
  ) None incoming
  |> Option.value ~default:Unknown

let has_side_effect = function
  | Store _ | Call _ -> true
  | _ -> false

let rec resolve_value (repl : value IntMap.t) (v : value) : value =
  match v with
  | VReg r ->
      begin match IntMap.find_opt r repl with
      | Some v' -> resolve_value repl v'
      | None -> v
      end
  | Imm _ | Global _ -> v

let apply_repl (f : func) (repl : value IntMap.t) : func =
  let rv = resolve_value repl in
  let ri instr = match instr with
    | Alloca _ -> instr
    | Load l   -> Load { l with ptr = rv l.ptr }
    | Store s  -> Store { val_ = rv s.val_; ptr = rv s.ptr }
    | Shl s    -> Shl { s with lhs = rv s.lhs; rhs = rv s.rhs }
    | AShr s   -> AShr { s with lhs = rv s.lhs; rhs = rv s.rhs }
    | And a    -> And { a with lhs = rv a.lhs; rhs = rv a.rhs }
    | Binop b  -> Binop { b with lhs = rv b.lhs; rhs = rv b.rhs }
    | Icmp c   -> Icmp { c with lhs = rv c.lhs; rhs = rv c.rhs }
    | Call c   -> Call { c with args = List.map rv c.args }
    | Phi p    -> Phi { p with incoming = List.map (fun (v, l) -> (rv v, l)) p.incoming }
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
      | Some dst when IntMap.mem dst repl && not (has_side_effect instr) -> None
      | _ -> Some (ri instr)
    ) bb.bb_instrs in
    (lbl, { bb with bb_instrs = new_instrs; bb_term = rt bb.bb_term })
  ) f.f_blocks in
  { f with f_blocks = new_blocks }

let run_on_func (global_consts : int StringMap.t) (f : func) : func =
  let state = ref IntMap.empty in
  let reachable = ref (IntSet.singleton f.f_entry) in

  List.iter (fun (_, r) ->
    state := IntMap.add r Overdefined !state
  ) f.f_params;

  let update_vreg dst value changed =
    let old = Option.value (IntMap.find_opt dst !state) ~default:Unknown in
    let joined = join_lattice old value in
    if joined <> old then begin
      state := IntMap.add dst joined !state;
      changed := true
    end
  in

  let mark_reachable lbl changed =
    if not (IntSet.mem lbl !reachable) then begin
      reachable := IntSet.add lbl !reachable;
      changed := true
    end
  in

  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (lbl, bb) ->
      if IntSet.mem lbl !reachable then begin
        List.iter (fun instr ->
          match instr with
          | Alloca { dst; _ } ->
              update_vreg dst Overdefined changed
            | Load { dst; ptr } ->
                update_vreg dst (lattice_of_load global_consts ptr) changed
          | Binop { dst; op; lhs; rhs } ->
              update_vreg dst (transfer_binop !state op lhs rhs) changed
          | Icmp { dst; cond; lhs; rhs } ->
              update_vreg dst (transfer_icmp !state cond lhs rhs) changed
          | Call { dst = Some dst; _ } ->
              update_vreg dst Overdefined changed
          | Call { dst = None; _ } ->
              ()
          | Phi { dst; incoming } ->
              update_vreg dst (transfer_phi !reachable !state incoming) changed
          | Shl { dst; _ } ->
              update_vreg dst Overdefined changed
          | AShr { dst; _ } ->
              update_vreg dst Overdefined changed
          | And { dst; _ } ->
              update_vreg dst Overdefined changed
          | Zext { dst; src } ->
              update_vreg dst (lattice_of_value !state src) changed
          | Copy { dst; src } ->
              update_vreg dst (lattice_of_value !state src) changed
          | Store _ ->
              ()
        ) bb.bb_instrs;
        begin match bb.bb_term with
        | Jump l ->
            mark_reachable l changed
        | Br (cond, t, f_lbl) ->
            begin match lattice_of_value !state cond with
            | Const 0 ->
                mark_reachable f_lbl changed
            | Const _ ->
                mark_reachable t changed
            | Overdefined ->
                mark_reachable t changed;
                mark_reachable f_lbl changed
            | Unknown ->
                ()
            end
        | Ret _ ->
            ()
        end
      end
    ) f.f_blocks
  done;

  let repl =
    IntMap.fold (fun r v acc ->
      match v with
      | Const n -> IntMap.add r (Imm n) acc
      | Unknown | Overdefined -> acc
    ) !state IntMap.empty
  in
  if IntMap.is_empty repl then f else apply_repl f repl

let run (m : module_) : module_ =
  let global_consts =
    List.fold_left
      (fun acc -> function
        | GConst { name; value } -> StringMap.add name value acc
        | GVar _ -> acc)
      StringMap.empty m.m_globals
  in
  { m with
    m_funcs = List.map (fun (n, f) -> (n, run_on_func global_consts f)) m.m_funcs
  }
