(* ToyC IR — 打印 *)

open Ir_types

let string_of_ir_type = function
  | I32  -> "i32"
  | I1   -> "i1"
  | Void -> "void"

let string_of_value = function
  | VReg r -> "%r" ^ string_of_int r
  | Imm n  -> string_of_int n
  | Global name -> "@" ^ name

let string_of_label l = "bb" ^ string_of_int l

let string_of_icmp_cond = function
  | IEq  -> "eq"
  | INe  -> "ne"
  | ISlt -> "slt"
  | ISle -> "sle"
  | ISgt -> "sgt"
  | ISge -> "sge"

let string_of_binary_op = function
  | Common.LOr  -> failwith "LOr should be lowered before IR"
  | Common.LAnd -> failwith "LAnd should be lowered before IR"
  | Common.Add  -> "add"
  | Common.Sub  -> "sub"
  | Common.Mul  -> "mul"
  | Common.Div  -> "sdiv"
  | Common.Mod  -> "srem"
  | Common.Eq | Common.Ne | Common.Lt | Common.Gt | Common.Le | Common.Ge ->
      failwith "comparison should be lowered to Icmp"

let string_of_instr = function
  | Alloca { dst; ty } ->
      Printf.sprintf "  %%r%d = alloca %s" dst (string_of_ir_type ty)
  | Load { dst; ptr } ->
      Printf.sprintf "  %%r%d = load %s" dst (string_of_value ptr)
  | Store { val_; ptr } ->
      Printf.sprintf "  store %s, %s" (string_of_value val_) (string_of_value ptr)
  | Binop { dst; op; lhs; rhs } ->
      Printf.sprintf "  %%r%d = %s %s, %s" dst (string_of_binary_op op)
        (string_of_value lhs) (string_of_value rhs)
  | Icmp { dst; cond; lhs; rhs } ->
      Printf.sprintf "  %%r%d = icmp %s %s, %s" dst (string_of_icmp_cond cond)
        (string_of_value lhs) (string_of_value rhs)
  | Call { dst = Some dst; fn; args } ->
      Printf.sprintf "  %%r%d = call @%s(%s)" dst fn
        (String.concat ", " (List.map string_of_value args))
  | Call { dst = None; fn; args } ->
      Printf.sprintf "  call @%s(%s)" fn
        (String.concat ", " (List.map string_of_value args))
  | Phi { dst; incoming } ->
      let pairs = List.map (fun (v, l) ->
        Printf.sprintf "[ %s, %%%s ]" (string_of_value v) (string_of_label l)
      ) incoming in
      Printf.sprintf "  %%r%d = phi %s" dst (String.concat ", " pairs)
  | Shl { dst; lhs; rhs } ->
      Printf.sprintf "  %%r%d = shl %s, %s" dst
        (string_of_value lhs) (string_of_value rhs)
  | AShr { dst; lhs; rhs } ->
      Printf.sprintf "  %%r%d = ashr %s, %s" dst
        (string_of_value lhs) (string_of_value rhs)
  | And { dst; lhs; rhs } ->
      Printf.sprintf "  %%r%d = and %s, %s" dst
        (string_of_value lhs) (string_of_value rhs)
  | Zext { dst; src } ->
      Printf.sprintf "  %%r%d = zext i1 %s to i32" dst (string_of_value src)
  | Copy { dst; src } ->
      Printf.sprintf "  %%r%d = copy %s" dst (string_of_value src)

let string_of_terminator = function
  | Ret None ->
      "  ret void"
  | Ret (Some v) ->
      Printf.sprintf "  ret %s" (string_of_value v)
  | Br (cond, t, f) ->
      Printf.sprintf "  br %s, %%%s, %%%s" (string_of_value cond)
        (string_of_label t) (string_of_label f)
  | Jump l ->
      Printf.sprintf "  jmp %%%s" (string_of_label l)

let string_of_block bb =
  let header = Printf.sprintf "%%%s:" (string_of_label bb.bb_label) in
  let body = List.map string_of_instr bb.bb_instrs in
  let term = string_of_terminator bb.bb_term in
  String.concat "\n" (header :: (body @ [ term ]))

let string_of_func f =
  let ret_str = match f.f_ret with Common.Int -> "i32" | Common.Void -> "void" in
  let params_str = String.concat ", " (List.map (fun (_, r) ->
    Printf.sprintf "i32 %%r%d" r
  ) f.f_params) in
  let header = Printf.sprintf "define %s @%s(%s) {" ret_str f.f_name params_str in
  let body = List.map (fun (_, bb) -> string_of_block bb) f.f_blocks in
  String.concat "\n" (header :: (body @ [ "}" ]))

let string_of_global = function
  | GVar { name; init } ->
      Printf.sprintf "@%s = global i32 %d" name init
  | GConst { name; value } ->
      Printf.sprintf "@%s = constant i32 %d" name value

let string_of_module m =
  let globals = String.concat "\n" (List.map string_of_global m.m_globals) in
  let funcs = String.concat "\n\n" (List.map (fun (_, f) -> string_of_func f) m.m_funcs) in
  if globals = "" then funcs
  else globals ^ "\n\n" ^ funcs
