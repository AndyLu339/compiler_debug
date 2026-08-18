(* ToyC 优化 — 常量传播
   Copy dst, Imm → 替换 dst 的所有 use 为 Imm, 删除 Copy
   仅传播 Imm 常量; VReg→VReg 的 copy 由 copy_prop 处理 *)

open Ir_types

module IntMap = Map.Make (Int)
module IntSet = Set.Make (Int)

let run_on_func (f : func) : func =
  (* 预扫描: 若同一 dst 被多条不同常量的 Copy 定义(非 SSA 多定义), 标记冲突并跳过传播,
     否则 fixpoint 会在这些值之间震荡死循环 *)
  let first_def = ref IntMap.empty in   (* dst → 第一个常量定义值 *)
  let conflict = ref IntSet.empty in
  List.iter (fun (_, bb) ->
    List.iter (fun instr ->
      match instr with
      | Copy { dst; src = Imm _ as imm } ->
          (match IntMap.find_opt dst !first_def with
           | None -> first_def := IntMap.add dst imm !first_def
           | Some v when v = imm -> ()
           | Some _ -> conflict := IntSet.add dst !conflict)
      | _ -> ()
    ) bb.bb_instrs
  ) f.f_blocks;
  let repl = ref IntMap.empty in
  (* 迭代处理链: %2 = copy Imm 5, %3 = copy %2 → %3 也变成 Imm 5 *)
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (_, bb) ->
      List.iter (fun instr ->
        match instr with
        | Copy { dst; src } when not (IntSet.mem dst !conflict) ->
            let ultimate = match src with
              | Imm _ | Global _ -> src
              | VReg r -> (match IntMap.find_opt r !repl with
                           | Some v -> v | None -> src)
            in
            (match ultimate with
             | Imm _ ->
                 (match IntMap.find_opt dst !repl with
                  | Some v when v = ultimate -> ()
                  | _ -> repl := IntMap.add dst ultimate !repl; changed := true)
             | _ -> ())
        | _ -> ()
      ) bb.bb_instrs
    ) f.f_blocks
  done;
  if IntMap.is_empty !repl then f
  else
    let rv v = match v with
      | VReg r -> (match IntMap.find_opt r !repl with Some v' -> v' | None -> v)
      | Imm _ | Global _ -> v
    in
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
        | Some dst when IntMap.mem dst !repl -> None
        | _ -> Some (ri instr)
      ) bb.bb_instrs in
      (lbl, { bb with bb_instrs = new_instrs; bb_term = rt bb.bb_term })
    ) f.f_blocks in
    { f with f_blocks = new_blocks }

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
