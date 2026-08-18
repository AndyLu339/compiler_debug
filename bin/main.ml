(* ToyC 编译器 — 主入口 *)

open Compiler_lib


let compile source : string =
  (* 1. 词法分析 *)
  let lexbuf = Lexing.from_string source in
  let ast = Parser.comp_unit Lexer.token lexbuf in
  (* 2. 语义分析 *)
  let ast = Semant.analyze ast in
  (* 3. IR 生成 *)
  let ir = Irgen.generate ast in
  (* 4. mem2reg — 内存模型到 SSA *)
  let ir = Mem2reg.promote ir in
  
  (* 5. IR 优化 *)
  let ir = Const_fold.run ir in      (* 常量折叠 *)
  let ir = Reassociate.run ir in      (* 重关联 *)
  let ir = Const_fold.run ir in       (* 再折叠, reassociate 暴露新常量 *)
  let ir = Inline.run ir in           (* 函数内联 *)
  let ir = Deadarg_elim.run ir in     (* 死参数消除  *)
  let ir = Globaldce.run ir in        (* 全局死代码消除 *)
  let ir = Algebraic.run ir in        (* 代数化简 *)
  let ir = Muldiv_opt.run ir in       (* 乘除优化: mul/div → shift *)
  let ir = Copy_prop.run ir in        (* Copy 传播 *)
  let ir = Cse.run ir in              (* 公共子表达式消除 *)
  let ir = Dce.run ir in              (* 死代码消除 *)
  let ir = Const_prop.run ir in       (* 常量传播 *)

  let ir = Sccp.run ir in             (* 稀疏条件常量传播 *)
  let ir = Branch_fold.run ir in      (* 常量分支折叠 + 不可达块删除 *)
  let ir = Dce.run ir in              (* 清理 Branch_fold 产生的死代码 *)
  let ir = Jump_thread.run ir in      (* 跳转穿透: Branch_fold 之后才有空块可穿 *)
  let ir = Simplifycfg.run ir in      (* 控制流化简: 块合并 + phi 简化 + 分支化简 *)

  (* loop opts *)
  let ir = Loop_canonicalize.run ir in (* 循环规范化，整理简单 while-loop 形状与出口 SSA *)
  let ir = Licm.run ir in             (* 循环不变量外提  *)
  let ir = Loop_unswitch.run ir in    (* 循环分支外提 *)
  let ir = Indvars.run ir in          (* 归纳变量化简 + 强度削减  *)
  let ir = Loop_eval.run ir in        (* 常量 trip loop 求值 / 归纳变量折叠 *)
  let ir = Loop_unroll.run ir in      (* 循环展开 *)
  (* let ir = Simplifycfg.run ir in   ← 展开后再跑会因线性扫描 spill 回退; 待图着色分配器(第四期 3.6)落地后再开 *)
  (* loop cleanup: 继续吃掉循环变换暴露出的常量、copy、死分支和死代码 *)
  let ir = Const_fold.run ir in
  let ir = Copy_prop.run ir in
  let ir = Sccp.run ir in
  let ir = Branch_fold.run ir in
  let ir = Dce.run ir in
  let ir = Algebraic.run ir in        (* 再代数化简 *)
  let ir = Dead_store_elim.run ir in  (* 循环变换后再做 DSE，收益更稳定 *)

  let ir = Gvn.run ir in              (* 全局值编号 *)
  let ir = Sccp.run ir in
  let ir = Algebraic.run ir in
  let ir = Jump_thread.run ir in
  (* let ir = Simplifycfg.run ir in   ← 同上: 在 Loop_unroll 之后, 待图着色分配器落地后再开 *)

  
    (* 6. 活跃区间分析 *)
  let intervals = Live_intervals.compute_module ir in
    (* 7. 寄存器分配 *)
  let ir, alloc = Regalloc.allocate ir intervals in
    (* 8. 代码生成 — IR → RISC-V *)
    Codegen.generate ir alloc

let () =
  let source =
    In_channel.input_all stdin
  in
  let asm = compile source in
  print_string asm
