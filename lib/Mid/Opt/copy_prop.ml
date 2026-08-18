(* ToyC 优化 — Copy 传播
   Copy dst, src → 把所有使用 dst 的地方替换为 src，删除 Copy
   通过构建 copy-chain 来处理链式 Copy *)

open Ir_types

module IntMap = Map.Make (Int)

let run_on_func (f : func) : func =
  (* 构建 copy-chain: vreg → 最终被拷贝的值 (可能是 Imm 或 VReg) *)
  let chain = ref IntMap.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (_, bb) ->
      List.iter (fun instr ->
        match instr with
        | Copy { dst; src } ->
            let ultimate = match src with
              | Imm _ | Global _ -> src
              | VReg r -> (match IntMap.find_opt r !chain with
                           | Some v -> v | None -> src)
            in
            (match IntMap.find_opt dst !chain with
             | Some v when v = ultimate -> ()
             | _ -> chain := IntMap.add dst ultimate !chain; changed := true)
        | _ -> ()
      ) bb.bb_instrs
    ) f.f_blocks
  done;
  if IntMap.is_empty !chain then f
  else
    let rv v = match v with
      | VReg r -> (match IntMap.find_opt r !chain with Some v' -> v' | None -> v)
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
        | Some dst when IntMap.mem dst !chain -> None
        | _ -> Some (ri instr)
      ) bb.bb_instrs in
      (lbl, { bb with bb_instrs = new_instrs; bb_term = rt bb.bb_term })
    ) f.f_blocks in
    { f with f_blocks = new_blocks }

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
