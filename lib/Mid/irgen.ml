(* ToyC IR 生成 — AST → IR 翻译 *)

open Common
open AST
open Ir_types
open Ir_builder

module StringMap = Map.Make (String)

(* ---------------------------------------------------------------------- *)
(* 翻译上下文                                                             *)
(* ---------------------------------------------------------------------- *)

type scope = value StringMap.t

type ctx = {
  builder : ir_builder;
  globals : value StringMap.t;
  func_rets : typ StringMap.t;
  mutable scopes : scope list;
  mutable break_lbl : label option;   (* 最近 while 的出口块 *)
  mutable continue_lbl : label option; (* 最近 while 的条件检查块 *)
}

let create_ctx globals func_rets : ctx =
  {
    builder = create_builder ();
    globals;
    func_rets;
    scopes = [ StringMap.empty ];
    break_lbl = None;
    continue_lbl = None;
  }

let enter_scope (ctx : ctx) =
  ctx.scopes <- StringMap.empty :: ctx.scopes

let leave_scope (ctx : ctx) =
  match ctx.scopes with
  | _ :: rest -> ctx.scopes <- rest
  | [] -> failwith "irgen.leave_scope: empty scope stack"

let with_scope (ctx : ctx) (f : unit -> unit) =
  enter_scope ctx;
  Fun.protect f ~finally:(fun () -> leave_scope ctx)

let bind_local (ctx : ctx) (name : string) (v : value) =
  match ctx.scopes with
  | cur :: outer ->
      ctx.scopes <- StringMap.add name v cur :: outer
  | [] ->
      failwith "irgen.bind_local: empty scope stack"

let rec lookup_scopes name = function
  | [] -> None
  | cur :: outer ->
      begin
        match StringMap.find_opt name cur with
        | Some _ as v -> v
        | None -> lookup_scopes name outer
      end

let lookup_var (ctx : ctx) (name : string) : value =
  match lookup_scopes name ctx.scopes with
  | Some v -> v
  | None ->
      begin
        match StringMap.find_opt name ctx.globals with
        | Some v -> v
        | None -> failwith ("undeclared identifier in irgen: " ^ name)
      end

let lookup_func_ret (ctx : ctx) (name : string) : typ =
  match lookup_scopes name ctx.scopes with
  | Some _ ->
      failwith ("identifier '" ^ name ^ "' is not a function in irgen")
  | None ->
      match StringMap.find_opt name ctx.func_rets with
  | Some ty -> ty
  | None -> failwith ("undeclared function in irgen: " ^ name)

(* ---------------------------------------------------------------------- *)
(* 全局初始化表达式                                                        *)
(* ---------------------------------------------------------------------- *)

let rec eval_global_init (consts : int StringMap.t) (e : expr) : int =
  match e.node with
  | Int n -> n
  | Var name ->
      begin
        match StringMap.find_opt name consts with
        | Some v -> v
        | None ->
            failwith ("global initializer must be constant: " ^ name)
      end
  | Binary (e1, LAnd, e2) ->
      let v1 = eval_global_init consts e1 in
      if v1 = 0 then 0
      else
        let v2 = eval_global_init consts e2 in
        if v2 <> 0 then 1 else 0
  | Binary (e1, LOr, e2) ->
      let v1 = eval_global_init consts e1 in
      if v1 <> 0 then 1
      else
        let v2 = eval_global_init consts e2 in
        if v2 <> 0 then 1 else 0
  | Unary (Pos, e1) ->
      eval_global_init consts e1
  | Unary (Neg, e1) ->
      -(eval_global_init consts e1)
  | Unary (Not, e1) ->
      if eval_global_init consts e1 = 0 then 1 else 0
  | Binary (e1, op, e2) ->
      let v1 = eval_global_init consts e1 in
      let v2 = eval_global_init consts e2 in
      begin
        match op with
        | Add -> v1 + v2
        | Sub -> v1 - v2
        | Mul -> v1 * v2
        | Div -> v1 / v2
        | Mod -> v1 mod v2
        | Eq -> if v1 = v2 then 1 else 0
        | Ne -> if v1 <> v2 then 1 else 0
        | Lt -> if v1 < v2 then 1 else 0
        | Gt -> if v1 > v2 then 1 else 0
        | Le -> if v1 <= v2 then 1 else 0
        | Ge -> if v1 >= v2 then 1 else 0
          | LAnd | LOr ->
              failwith "unreachable: short-circuit operators handled above"
      end
  | Call _ ->
      failwith "function call not allowed in global initializer"

(* ---------------------------------------------------------------------- *)
(* binary_op → icmp_cond 辅助映射                                         *)
(* ---------------------------------------------------------------------- *)

let binop_to_icmp_cond (op : binary_op) : icmp_cond =
  match op with
  | Eq -> IEq
  | Ne -> INe
  | Lt -> ISlt
  | Gt -> ISgt
  | Le -> ISle
  | Ge -> ISge
  | _  -> failwith "not a comparison operator"

(* ---------------------------------------------------------------------- *)
(* 表达式翻译 — 返回持有结果的 value（始终为 i32）                          *)
(* ---------------------------------------------------------------------- *)

let rec translate_expr (ctx : ctx) (e : expr) : value =
  match e.node with
  | Var name ->
      let ptr = lookup_var ctx name in
      VReg (build_load ctx.builder ptr)

  | Int n ->
      Imm n

  | Binary (e1, LAnd, e2) ->
      let rhs_blk = new_block ctx.builder in
      let short_blk = new_block ctx.builder in
      let merge_blk = new_block ctx.builder in
      translate_cond ctx e1 rhs_blk short_blk;
      set_insert_point ctx.builder rhs_blk;
      let v_b = translate_expr ctx e2 in
      let i1_b = build_icmp ctx.builder INe v_b (Imm 0) in
      let v_b32 = build_zext ctx.builder (VReg i1_b) in
      let rhs_end_lbl = (get_insert_block ctx.builder).bb_label in
      build_jump ctx.builder merge_blk;
      set_insert_point ctx.builder short_blk;
      build_jump ctx.builder merge_blk;
      set_insert_point ctx.builder merge_blk;
      VReg (build_phi ctx.builder [ (VReg v_b32, rhs_end_lbl); (Imm 0, short_blk) ])

  | Binary (e1, LOr, e2) ->
      let short_blk = new_block ctx.builder in
      let rhs_blk = new_block ctx.builder in
      let merge_blk = new_block ctx.builder in
      translate_cond ctx e1 short_blk rhs_blk;
      set_insert_point ctx.builder short_blk;
      build_jump ctx.builder merge_blk;
      set_insert_point ctx.builder rhs_blk;
      let v_b = translate_expr ctx e2 in
      let i1_b = build_icmp ctx.builder INe v_b (Imm 0) in
      let v_b32 = build_zext ctx.builder (VReg i1_b) in
      let rhs_end_lbl = (get_insert_block ctx.builder).bb_label in
      build_jump ctx.builder merge_blk;
      set_insert_point ctx.builder merge_blk;
      VReg (build_phi ctx.builder [ (Imm 1, short_blk); (VReg v_b32, rhs_end_lbl) ])

  | Binary (e1, op, e2) ->
      let v1 = translate_expr ctx e1 in
      let v2 = translate_expr ctx e2 in
      begin
        match op with
        | Add | Sub | Mul | Div | Mod ->
            VReg (build_binop ctx.builder op v1 v2)
        | Eq | Ne | Lt | Gt | Le | Ge ->
            let cond = binop_to_icmp_cond op in
            let i1 = build_icmp ctx.builder cond v1 v2 in
            VReg (build_zext ctx.builder (VReg i1))
        | LAnd | LOr ->
            failwith "unreachable: LAnd/LOr caught above"
      end

  | Unary (Neg, e1) ->
      let v = translate_expr ctx e1 in
      VReg (build_binop ctx.builder Sub (Imm 0) v)

  | Unary (Pos, e1) ->
      translate_expr ctx e1

  | Unary (Not, e1) ->
      let v = translate_expr ctx e1 in
      let i1 = build_icmp ctx.builder IEq v (Imm 0) in
      VReg (build_zext ctx.builder (VReg i1))

  | Call (fn, args) ->
      let vargs = List.map (translate_expr ctx) args in
      begin
        match lookup_func_ret ctx fn with
        | Void ->
            failwith ("void function used as value in irgen: " ^ fn)
        | Int ->
            VReg (build_call ctx.builder fn vargs)
      end

and translate_cond (ctx : ctx) (e : expr) (true_lbl : label) (false_lbl : label) : unit =
  match e.node with
  | Binary (e1, LAnd, e2) ->
      let check_rhs = new_block ctx.builder in
      translate_cond ctx e1 check_rhs false_lbl;
      set_insert_point ctx.builder check_rhs;
      translate_cond ctx e2 true_lbl false_lbl

  | Binary (e1, LOr, e2) ->
      let check_rhs = new_block ctx.builder in
      translate_cond ctx e1 true_lbl check_rhs;
      set_insert_point ctx.builder check_rhs;
      translate_cond ctx e2 true_lbl false_lbl

  | Unary (Not, e1) ->
      translate_cond ctx e1 false_lbl true_lbl

  | Binary (e1, op, e2)
    when (match op with Eq | Ne | Lt | Gt | Le | Ge -> true | _ -> false) ->
      (* 关系表达式直接生成 icmp + br，避免 translate_expr 的 zext 后再判真 *)
      let v1 = translate_expr ctx e1 in
      let v2 = translate_expr ctx e2 in
      let cond = binop_to_icmp_cond op in
      let i1 = build_icmp ctx.builder cond v1 v2 in
      build_br ctx.builder (VReg i1) true_lbl false_lbl

  | _ ->
      let v = translate_expr ctx e in
      let i1 = build_icmp ctx.builder INe v (Imm 0) in
      build_br ctx.builder (VReg i1) true_lbl false_lbl

(* ---------------------------------------------------------------------- *)
(* 变量声明：alloca + store init                                          *)
(* ---------------------------------------------------------------------- *)

let translate_var_decl (ctx : ctx) (name : string) (init : expr) =
  let slot = build_alloca ctx.builder I32 in
  (* 局部名字从声明开始就进入当前作用域，
     initializer 中的同名引用优先绑定到新声明，而不是外层全局/局部。 *)
  bind_local ctx name (VReg slot);
  let init_val = translate_expr ctx init in
  build_store ctx.builder init_val (VReg slot)

(* ---------------------------------------------------------------------- *)
(* 辅助：检查当前基本块是否未被终结                                       *)
(* ---------------------------------------------------------------------- *)

let block_is_open (b : ir_builder) : bool =
  let bb = get_insert_block b in
  match bb.bb_term with
  | Jump l -> l = bb.bb_label
  | Ret _ | Br _ -> false

(* ---------------------------------------------------------------------- *)
(* 语句翻译                                                               *)
(* ---------------------------------------------------------------------- *)

let rec translate_stmt_list (ctx : ctx) (stmts : stmt list) : unit =
  match stmts with
  | [] -> ()
  | s :: rest ->
      if block_is_open ctx.builder then begin
        translate_stmt ctx s;
        translate_stmt_list ctx rest
      end

and translate_stmt (ctx : ctx) (s : stmt) : unit =
  if not (block_is_open ctx.builder) then
    ()
  else
    match s.node with
    | Block stmts ->
        with_scope ctx (fun () -> translate_stmt_list ctx stmts)

    | Empty ->
        ()

    | ExprStmt e ->
        begin
          match e.node with
          | Call (fn, args) ->
              let vargs = List.map (translate_expr ctx) args in
              begin
                match lookup_func_ret ctx fn with
                | Void -> build_void_call ctx.builder fn vargs
                | Int -> ignore (build_call ctx.builder fn vargs)
              end
          | _ ->
              ignore (translate_expr ctx e)
        end

    | Assign (name, e) ->
        let ptr = lookup_var ctx name in
        let v = translate_expr ctx e in
        build_store ctx.builder v ptr

    | DeclStmt { node = VarDecl d; _ } ->
        translate_var_decl ctx d.var_name d.var_init

    | DeclStmt { node = ConstDecl d; _ } ->
        translate_var_decl ctx d.const_name d.const_init

    | Return (Some e) ->
        let v = translate_expr ctx e in
        build_ret ctx.builder (Some v)

    | Return None ->
        build_ret ctx.builder None

    | If (cond, then_stmt, Some else_stmt) ->
        let then_blk = new_block ctx.builder in
        let else_blk = new_block ctx.builder in
        let merge_blk = new_block ctx.builder in
        translate_cond ctx cond then_blk else_blk;
        set_insert_point ctx.builder then_blk;
        translate_stmt ctx then_stmt;
        if block_is_open ctx.builder then
          build_jump ctx.builder merge_blk;
        set_insert_point ctx.builder else_blk;
        translate_stmt ctx else_stmt;
        if block_is_open ctx.builder then
          build_jump ctx.builder merge_blk;
        set_insert_point ctx.builder merge_blk

    | If (cond, then_stmt, None) ->
        let then_blk = new_block ctx.builder in
        let merge_blk = new_block ctx.builder in
        translate_cond ctx cond then_blk merge_blk;
        set_insert_point ctx.builder then_blk;
        translate_stmt ctx then_stmt;
        if block_is_open ctx.builder then
          build_jump ctx.builder merge_blk;
        set_insert_point ctx.builder merge_blk

    | While (cond, body) ->
        let header_blk = new_block ctx.builder in
        let body_blk   = new_block ctx.builder in
        let exit_blk   = new_block ctx.builder in
        build_jump ctx.builder header_blk;
        set_insert_point ctx.builder header_blk;
        translate_cond ctx cond body_blk exit_blk;
        set_insert_point ctx.builder body_blk;
        let saved_break = ctx.break_lbl in
        let saved_continue = ctx.continue_lbl in
        ctx.break_lbl <- Some exit_blk;
        ctx.continue_lbl <- Some header_blk;
        translate_stmt ctx body;
        ctx.break_lbl <- saved_break;
        ctx.continue_lbl <- saved_continue;
        if block_is_open ctx.builder then
          build_jump ctx.builder header_blk;
        set_insert_point ctx.builder exit_blk

    | Break ->
        begin
          match ctx.break_lbl with
          | Some lbl -> build_jump ctx.builder lbl
          | None -> failwith "break outside of loop"
        end

    | Continue ->
        begin
          match ctx.continue_lbl with
          | Some lbl -> build_jump ctx.builder lbl
          | None -> failwith "continue outside of loop"
        end

(* ---------------------------------------------------------------------- *)
(* 函数翻译                                                               *)
(* ---------------------------------------------------------------------- *)

let translate_func (globals : value StringMap.t) (func_rets : typ StringMap.t) (fd : func_def) : func =
  let ctx = create_ctx globals func_rets in
  let entry_lbl = new_block ctx.builder in
  set_insert_point ctx.builder entry_lbl;

  let param_vregs =
    List.map
      (fun p ->
        let vreg = fresh_vreg ctx.builder in
        (p.param_name, vreg))
      fd.func_params
  in

  List.iter
    (fun (name, vreg) ->
      let slot = build_alloca ctx.builder I32 in
      build_store ctx.builder (VReg vreg) (VReg slot);
      bind_local ctx name (VReg slot))
    param_vregs;

  with_scope ctx (fun () -> List.iter (translate_stmt ctx) fd.func_body);

  if block_is_open ctx.builder && fd.func_ret = Void then
    build_ret ctx.builder None;

  {
    f_name   = fd.func_name;
    f_ret    = fd.func_ret;
    f_params = param_vregs;
    f_blocks = collect_blocks ctx.builder;
    f_entry  = entry_lbl;
    f_max_vreg = ctx.builder.next_vreg - 1;
    f_max_label = ctx.builder.next_label - 1;
  }

(* ---------------------------------------------------------------------- *)
(* 顶层入口                                                               *)
(* ---------------------------------------------------------------------- *)

let generate (cu : comp_unit) : module_ =
  let globals = ref [] in
  let funcs   = ref [] in
  let global_values = ref StringMap.empty in
  let global_consts = ref StringMap.empty in
  let func_rets =
    List.fold_left
      (fun acc item ->
        match item.node with
        | TopFunc fd -> StringMap.add fd.func_name fd.func_ret acc
        | TopDecl _ -> acc)
      StringMap.empty cu
  in

  List.iter
    (fun item ->
      match item.node with
      | TopDecl { node = VarDecl d; _ } ->
          let init = eval_global_init !global_consts d.var_init in
          globals := GVar { name = d.var_name; init } :: !globals;
          global_values := StringMap.add d.var_name (Global d.var_name) !global_values

      | TopDecl { node = ConstDecl d; _ } ->
          let value = eval_global_init !global_consts d.const_init in
          globals := GConst { name = d.const_name; value } :: !globals;
          global_values := StringMap.add d.const_name (Global d.const_name) !global_values;
          global_consts := StringMap.add d.const_name value !global_consts

      | TopFunc fd ->
          let func = translate_func !global_values func_rets fd in
          funcs := (fd.func_name, func) :: !funcs)
    cu;

  { m_globals = List.rev !globals; m_funcs = List.rev !funcs }
