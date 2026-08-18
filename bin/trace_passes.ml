open Compiler_lib

type stage = {
  name : string;
  ir : Ir_types.module_;
}

let print_module_with_entry (m : Ir_types.module_) =
  let buf = Buffer.create 4096 in
  List.iter (fun g ->
    Buffer.add_string buf (Ir_print.string_of_global g);
    Buffer.add_char buf '\n'
  ) m.m_globals;
  List.iter (fun (_, (f : Ir_types.func)) ->
    Buffer.add_string buf (Printf.sprintf "; entry %s\n" (Ir_print.string_of_label f.f_entry));
    Buffer.add_string buf (Ir_print.string_of_func f);
    Buffer.add_string buf "\n\n"
  ) m.m_funcs;
  Buffer.contents buf

let add_stage acc name ir =
  acc @ [ { name; ir } ]

let front source : stage list =
  let lexbuf = Lexing.from_string source in
  let ast = Parser.comp_unit Lexer.token lexbuf in
  let ast = Semant.analyze ast in
  let ir = Irgen.generate ast in
  let stages = [ { name = "irgen"; ir } ] in
  let ir = Mem2reg.promote ir in
  add_stage stages "mem2reg" ir

let run_pipeline (initial : stage list) : stage list =
  let last_ir stages = (List.hd (List.rev stages)).ir in
  let run name pass stages =
    let ir = pass (last_ir stages) in
    add_stage stages name ir
  in
  initial
  |> run "const_fold_1" Const_fold.run
  |> run "reassociate" Reassociate.run
  |> run "const_fold_2" Const_fold.run
  |> run "inline" Inline.run
  |> run "deadarg_elim" Deadarg_elim.run
  |> run "globaldce" Globaldce.run
  |> run "algebraic_1" Algebraic.run
  |> run "muldiv_opt" Muldiv_opt.run
  |> run "copy_prop_1" Copy_prop.run
  |> run "cse" Cse.run
  |> run "dce_1" Dce.run
  |> run "const_prop" Const_prop.run
  |> run "sccp_1" Sccp.run
  |> run "branch_fold_1" Branch_fold.run
  |> run "dce_2" Dce.run
  |> run "jump_thread_1" Jump_thread.run
  |> run "simplifycfg_1" Simplifycfg.run
  |> run "dead_store_elim" Dead_store_elim.run
  |> run "licm" Licm.run
  |> run "loop_unswitch" Loop_unswitch.run
  |> run "loop_eval" Loop_eval.run
  |> run "indvars" Indvars.run
  |> run "loop_unroll" Loop_unroll.run
  |> run "const_fold_3" Const_fold.run
  |> run "copy_prop_2" Copy_prop.run
  |> run "sccp_2" Sccp.run
  |> run "branch_fold_2" Branch_fold.run
  |> run "dce_3" Dce.run
  |> run "algebraic_2" Algebraic.run
  |> run "gvn" Gvn.run
  |> run "sccp_3" Sccp.run
  |> run "algebraic_3" Algebraic.run
  |> run "jump_thread_2" Jump_thread.run

let () =
  let source = In_channel.input_all stdin in
  let stages = front source |> run_pipeline in
  List.iter (fun { name; ir } ->
    Printf.printf "===== %s =====\n" name;
    print_string (print_module_with_entry ir)
  ) stages
