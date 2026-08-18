(* 临时调试工具: 打印 tail_call_elim 之后的 IR, 以及最终汇编。
   用法: dune exec bin/dump_ir.exe [ir|asm] < test.c *)

open Compiler_lib

let front source : Ir_types.module_ =
  let lexbuf = Lexing.from_string source in
  let ast = Parser.comp_unit Lexer.token lexbuf in
  let ast = Semant.analyze ast in
  let ir = Irgen.generate ast in
  Mem2reg.promote ir

let after_tce ir =
  let ir = Const_fold.run ir in
  let ir = Reassociate.run ir in
  let ir = Const_fold.run ir in
  let ir = Tail_call_elim.run ir in
  ir

let full_opt ir =
  let ir = after_tce ir in
  let ir = Inline.run ir in
  let ir = Algebraic.run ir in
  let ir = Muldiv_opt.run ir in
  let ir = Copy_prop.run ir in
  let ir = Cse.run ir in
  let ir = Dce.run ir in
  let ir = Const_prop.run ir in
  let ir = Sccp.run ir in
  let ir = Branch_fold.run ir in
  let ir = Dce.run ir in
  let ir = Jump_thread.run ir in
  let ir = Simplifycfg.run ir in
  let ir = Loop_canonicalize.run ir in
  let ir = Licm.run ir in
  let ir = Loop_unswitch.run ir in
  let ir = Indvars.run ir in
  let ir = Loop_eval.run ir in
  let ir = Loop_unroll.run ir in
  let ir = Const_fold.run ir in
  let ir = Copy_prop.run ir in
  let ir = Sccp.run ir in
  let ir = Branch_fold.run ir in
  let ir = Dce.run ir in
  let ir = Algebraic.run ir in
  let ir = Dead_store_elim.run ir in
  ir

let full_compile ir =
  let ir = full_opt ir in
  let intervals = Live_intervals.compute_module ir in
  let ir, alloc = Regalloc.allocate ir intervals in
  Codegen.generate ir alloc

(* 打印带 entry 标记的模块, 供解释器确定入口块 *)
let print_module_with_entry (m : Ir_types.module_) =
  let buf = Buffer.create 4096 in
  List.iter (fun g -> Buffer.add_string buf (Ir_print.string_of_global g ^ "\n")) m.m_globals;
  List.iter (fun (_, (f : Ir_types.func)) ->
    Buffer.add_string buf (Printf.sprintf "; entry %s\n" (Ir_print.string_of_label f.f_entry));
    Buffer.add_string buf (Ir_print.string_of_func f);
    Buffer.add_string buf "\n"
  ) m.m_funcs;
  Buffer.contents buf

let tce_asm ir =
  let ir = after_tce ir in
  let intervals = Live_intervals.compute_module ir in
  let ir, alloc = Regalloc.allocate ir intervals in
  Codegen.generate ir alloc

let () =
  let mode = if Array.length Sys.argv > 1 then Sys.argv.(1) else "ir" in
  let source = In_channel.input_all stdin in
  let ir = front source in
  match mode with
  | "asm" -> print_string (full_compile ir)
  | "final" -> print_string (print_module_with_entry (full_opt ir))
  | "tce_asm" -> print_string (tce_asm ir)
  | "pre" -> print_string (print_module_with_entry ir)
  | _ -> print_string (print_module_with_entry (after_tce ir))
