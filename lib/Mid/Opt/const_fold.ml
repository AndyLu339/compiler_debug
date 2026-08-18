(* ToyC 优化 — 常量折叠
   Binop/Icmp 两侧都是 Imm → 编译期计算, 替换所有 use, 删除原指令 *)

open Ir_types
open Common

module IntMap = Map.Make (Int)

(* 折叠时用 Common.wrap32 模拟 RV32 的 32 位回绕，
   避免溢出常量被误当作 64 位值参与后续比较。 *)

let eval_binop (op : binary_op) (l : int) (r : int) : int =
  let l = wrap32 l and r = wrap32 r in
  match op with
  | Add -> wrap32 (l + r) | Sub -> wrap32 (l - r) | Mul -> wrap32 (l * r)
  | Div -> wrap32 (l / r) | Mod -> wrap32 (l mod r)
  | Eq  -> if l = r  then 1 else 0
  | Ne  -> if l <> r then 1 else 0
  | Lt  -> if l < r  then 1 else 0
  | Gt  -> if l > r  then 1 else 0
  | Le  -> if l <= r then 1 else 0
  | Ge  -> if l >= r then 1 else 0
  | LAnd | LOr -> failwith "LAnd/LOr should be lowered before IR"

(* 检查是否应该折叠：除数为 0 时不折叠，保留到运行时 *)
let can_fold_binop (op : binary_op) (_l : int) (r : int) : bool =
  match op with
  | Div | Mod -> wrap32 r <> 0
  | _ -> true

let eval_icmp (cond : icmp_cond) (l : int) (r : int) : int =
  let l = wrap32 l and r = wrap32 r in
  match cond with
  | IEq  -> if l = r  then 1 else 0  | INe  -> if l <> r then 1 else 0
  | ISlt -> if l < r  then 1 else 0  | ISle -> if l <= r then 1 else 0
  | ISgt -> if l > r  then 1 else 0  | ISge -> if l >= r then 1 else 0

(* 在函数内替换 vreg → value, 并删除被替换 dst 的指令 *)
let apply_repl (f : func) (repl : value IntMap.t) : func =
  let rv v = match v with
    | VReg r -> (match IntMap.find_opt r repl with Some v' -> v' | None -> v)
    | Imm _ | Global _ -> v
  in
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

let run_on_func (f : func) : func =
  let rec fixpoint (f : func) : func =
    let repl = ref IntMap.empty in
    List.iter (fun (_, bb) ->
      List.iter (fun instr ->
        match instr with
        | Binop { dst; op; lhs = Imm a; rhs = Imm b }
          when can_fold_binop op a b ->
            repl := IntMap.add dst (Imm (eval_binop op a b)) !repl
        | Icmp { dst; cond; lhs = Imm a; rhs = Imm b } ->
            repl := IntMap.add dst (Imm (eval_icmp cond a b)) !repl
        | Zext { dst; src = Imm v } ->
            repl := IntMap.add dst (Imm (v land 1)) !repl
        | _ -> ()
      ) bb.bb_instrs
    ) f.f_blocks;
    if IntMap.is_empty !repl then f
    else fixpoint (apply_repl f !repl)
  in
  fixpoint f

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
