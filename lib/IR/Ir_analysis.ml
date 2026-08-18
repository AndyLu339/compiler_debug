(* ToyC IR — def-use 分析 & replace_all_uses *)

open Ir_types

module VMap = Map.Make(struct type t = int let compare = compare end)

type def_use = {
  (* vreg → 定义位置 (block_label, instr_index) *)
  def_site : (label * int) VMap.t;
  (* vreg → 使用位置列表 *)
  use_sites : (label * int) list VMap.t;
}

(* 遍历整个 module，为每个 vreg 收集 def-site 和 use-site *)
let build_def_use (m : module_) : def_use =
  let def_site = ref VMap.empty in
  let use_site = ref VMap.empty in
  let add_use vreg (bl, idx) =
    use_site := VMap.update vreg (function
      | None   -> Some [ (bl, idx) ]
      | Some l -> Some ((bl, idx) :: l)
    ) !use_site
  in
  List.iter (fun (_, f) ->
    List.iter (fun (_, bb) ->
      (* 非终结指令 *)
      List.iteri (fun idx instr ->
        Option.iter (fun dst ->
          def_site := VMap.add dst (bb.bb_label, idx) !def_site
        ) (instr_dst instr);
        List.iter (function
          | VReg r -> add_use r (bb.bb_label, idx)
          | Imm _ | Global _ -> ()
        ) (instr_uses instr)
      ) bb.bb_instrs;
      (* 终结指令 (idx = -1 表示 terminator) *)
      List.iter (function
        | VReg r -> add_use r (bb.bb_label, -1)
        | Imm _ | Global _ -> ()
      ) (terminator_uses bb.bb_term)
    ) f.f_blocks
  ) m.m_funcs;
  { def_site = !def_site; use_sites = !use_site }

(* 在 value 中替换 vreg *)
let replace_vreg_in_value (old_vreg : int) (new_val : value) (v : value) : value =
  match v with
  | VReg r when r = old_vreg -> new_val
  | _ -> v

let replace_vreg_in_instr (old_vreg : int) (new_val : value) (i : instr) : instr =
  let r v = replace_vreg_in_value old_vreg new_val v in
  match i with
  | Alloca _ -> i
  | Load l   -> Load { l with ptr = r l.ptr }
  | Store s  -> Store { val_ = r s.val_; ptr = r s.ptr }
  | Binop b  -> Binop { b with lhs = r b.lhs; rhs = r b.rhs }
  | Icmp c   -> Icmp { c with lhs = r c.lhs; rhs = r c.rhs }
  | Call c   -> Call { c with args = List.map r c.args }
  | Phi p    -> Phi { p with incoming = List.map (fun (v, l) -> (r v, l)) p.incoming }
  | Shl s    -> Shl { s with lhs = r s.lhs; rhs = r s.rhs }
  | AShr s   -> AShr { s with lhs = r s.lhs; rhs = r s.rhs }
  | And a    -> And { a with lhs = r a.lhs; rhs = r a.rhs }
  | Zext z   -> Zext { z with src = r z.src }
  | Copy c   -> Copy { c with src = r c.src }

let replace_vreg_in_terminator (old_vreg : int) (new_val : value) (t : terminator) : terminator =
  let r v = replace_vreg_in_value old_vreg new_val v in
  match t with
  | Ret (Some v)    -> Ret (Some (r v))
  | Ret None        -> Ret None
  | Br (cond, t, f) -> Br (r cond, t, f)
  | Jump _          -> t
