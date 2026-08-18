(* ToyC IR — IRBuilder 构造器 *)

open Ir_types
open Common

type ir_builder = {
  mutable next_vreg : int;                        (* 自动分配 vreg 序号 *)
  mutable next_label : int;                       (* 自动分配 label 序号 *)
  mutable cur_label : label;                      (* 当前插入目标基本块 *)
  mutable cur_blocks : (label, basic_block) Hashtbl.t;
}

let create_builder () : ir_builder = {
  next_vreg = 0;
  next_label = 0;
  cur_label = 0;
  cur_blocks = Hashtbl.create 16;
}

(* 申请一个新的虚拟寄存器编号 *)
let fresh_vreg (b : ir_builder) : int =
  let r = b.next_vreg in
  b.next_vreg <- r + 1;
  r

(* 申请一个新的基本块标签 *)
let fresh_label (b : ir_builder) : label =
  let l = b.next_label in
  b.next_label <- l + 1;
  l

(* 设置后续指令插入到哪个基本块 *)
let set_insert_point (b : ir_builder) (lbl : label) =
  b.cur_label <- lbl

(* 获取当前正在插入的基本块 *)
let get_insert_block (b : ir_builder) : basic_block =
  Hashtbl.find b.cur_blocks b.cur_label

(* 向当前基本块末尾追加一条普通指令 *)
let emit (b : ir_builder) (i : instr) =
  let bb = get_insert_block b in
  Hashtbl.replace b.cur_blocks b.cur_label
    { bb with bb_instrs = bb.bb_instrs @ [ i ] }

(* 设置当前基本块的终结指令（跳转/返回） *)
let emit_term (b : ir_builder) (t : terminator) =
  let bb = get_insert_block b in
  Hashtbl.replace b.cur_blocks b.cur_label
    { bb with bb_term = t }

(* 指令构造 *)

(* 在栈上分配一个 ty 类型的局部变量，返回其地址的虚拟寄存器 *)
let build_alloca (b : ir_builder) (ty : ir_type) : int =
  let dst = fresh_vreg b in
  emit b (Alloca { dst; ty });
  dst

(* 从 ptr 地址加载值到新虚拟寄存器 *)
let build_load (b : ir_builder) (ptr : value) : int =
  let dst = fresh_vreg b in
  emit b (Load { dst; ptr });
  dst

(* 将 val_ 写入 ptr 地址 *)
let build_store (b : ir_builder) (val_ : value) (ptr : value) =
  emit b (Store { val_; ptr })

(* 二元运算：lhs op rhs，结果写入新虚拟寄存器 *)
let build_binop (b : ir_builder) (op : binary_op) (lhs : value) (rhs : value) : int =
  let dst = fresh_vreg b in
  emit b (Binop { dst; op; lhs; rhs });
  dst

(* 整数比较：lhs cond rhs，结果 (0/1) 写入新虚拟寄存器 *)
let build_icmp (b : ir_builder) (cond : icmp_cond) (lhs : value) (rhs : value) : int =
  let dst = fresh_vreg b in
  emit b (Icmp { dst; cond; lhs; rhs });
  dst

(* 调用有返回值的函数，结果写入新虚拟寄存器 *)
let build_call (b : ir_builder) (fn : string) (args : value list) : int =
  let dst = fresh_vreg b in
  emit b (Call { dst = Some dst; fn; args });
  dst

(* 调用 void 函数，无返回值 *)
let build_void_call (b : ir_builder) (fn : string) (args : value list) =
  emit b (Call { dst = None; fn; args })

(* φ 节点：根据来源基本块选择值，结果写入新虚拟寄存器 *)
let build_phi (b : ir_builder) (incoming : (value * label) list) : int =
  let dst = fresh_vreg b in
  emit b (Phi { dst; incoming });
  dst

(* 零扩展：将 i1 类型值扩展为 i32 *)
let build_zext (b : ir_builder) (src : value) : int =
  let dst = fresh_vreg b in
  emit b (Zext { dst; src });
  dst

(* 移位左：lhs << rhs，结果写入新虚拟寄存器 *)
let build_shl (b : ir_builder) (lhs : value) (rhs : value) : int =
  let dst = fresh_vreg b in
  emit b (Shl { dst; lhs; rhs });
  dst

(* 算术右移：lhs >> rhs (符号扩展)，结果写入新虚拟寄存器 *)
let build_ashr (b : ir_builder) (lhs : value) (rhs : value) : int =
  let dst = fresh_vreg b in
  emit b (AShr { dst; lhs; rhs });
  dst

(* 按位与：lhs & rhs，结果写入新虚拟寄存器 *)
let build_and (b : ir_builder) (lhs : value) (rhs : value) : int =
  let dst = fresh_vreg b in
  emit b (And { dst; lhs; rhs });
  dst

(* 拷贝：将 src 的值复制到新虚拟寄存器 *)
let build_copy (b : ir_builder) (src : value) : int =
  let dst = fresh_vreg b in
  emit b (Copy { dst; src });
  dst

(* 终结指令 *)

(* 函数返回，可选返回值 *)
let build_ret (b : ir_builder) (v : value option) =
  emit_term b (Ret v)

(* 条件跳转：cond 非零跳 t_lbl，否则跳 f_lbl *)
let build_br (b : ir_builder) (cond : value) (t_lbl : label) (f_lbl : label) =
  emit_term b (Br (cond, t_lbl, f_lbl))

(* 无条件跳转 *)
let build_jump (b : ir_builder) (lbl : label) =
  emit_term b (Jump lbl)

(* 基本块管理 *)

(* 创建一个新的基本块并以 Jump 自身作为占位终结指令，返回其标签 *)
let new_block (b : ir_builder) : label =
  let lbl = fresh_label b in
  Hashtbl.add b.cur_blocks lbl { bb_label = lbl; bb_instrs = []; bb_term = Jump lbl };
  lbl

(* 收集所有基本块，按标签号排序后返回 *)
let collect_blocks (b : ir_builder) : (label * basic_block) list =
  Hashtbl.fold (fun lbl bb acc -> (lbl, bb) :: acc) b.cur_blocks []
  |> List.sort (fun (a, _) (b, _) -> compare a b)
