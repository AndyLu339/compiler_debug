(* ToyC 语义分析 *)

open AST
open Common
open Symtab

(* ---------------------------------------------------------------------- *)
(* 错误                                                               *)
(* ---------------------------------------------------------------------- *)

let semant_error ?loc msg =
  let prefix = match loc with
    | Some l -> Printf.sprintf "Semantic error at %s: " (string_of_loc l)
    | None -> "Semantic error: "
  in
  failwith (prefix ^ msg)

(* ---------------------------------------------------------------------- *)
(* 常量表达式求值                                                         *)
(*   const 初始化表达式的值在编译期确定                                     *)
(* ---------------------------------------------------------------------- *)

let rec eval_const_expr (st : t) (e : expr) : int =
  match e.node with
  | Int n -> n
  | Var id ->
    (match lookup id st with
     | Some (ConstInfo { value }) -> value
     | Some _ -> semant_error ~loc:e.loc ("constant expression expected, got variable: " ^ id)
     | None -> semant_error ~loc:e.loc ("undeclared identifier in const: " ^ id))
  | Binary (e1, LAnd, e2) ->
    let v1 = eval_const_expr st e1 in
    if v1 = 0 then 0
    else
      let v2 = eval_const_expr st e2 in
      if v2 <> 0 then 1 else 0
  | Binary (e1, LOr, e2) ->
    let v1 = eval_const_expr st e1 in
    if v1 <> 0 then 1
    else
      let v2 = eval_const_expr st e2 in
      if v2 <> 0 then 1 else 0
  | Binary (e1, op, e2) ->
    let v1 = eval_const_expr st e1 in
    let v2 = eval_const_expr st e2 in
    eval_const_binop e.loc op v1 v2
  | Unary (op, e') ->
    let v = eval_const_expr st e' in
    eval_const_unop op v
  | Call _ -> semant_error ~loc:e.loc "function call not allowed in constant expression"

and eval_const_binop (loc : loc) (op : binary_op) (a : int) (b : int) : int =
  match op with
  | Add -> a + b
  | Sub -> a - b
  | Mul -> a * b
  | Div -> if b = 0 then semant_error ~loc "division by zero in constant" else a / b
  | Mod -> if b = 0 then semant_error ~loc "modulo by zero in constant" else a mod b
  | Eq  -> if a = b then 1 else 0
  | Ne  -> if a <> b then 1 else 0
  | Lt  -> if a < b then 1 else 0
  | Gt  -> if a > b then 1 else 0
  | Le  -> if a <= b then 1 else 0
  | Ge  -> if a >= b then 1 else 0
  | LAnd -> (if a <> 0 then 1 else 0) * (if b <> 0 then 1 else 0)
  | LOr  -> if a <> 0 || b <> 0 then 1 else 0

and eval_const_unop (op : unary_op) (a : int) : int =
  match op with
  | Pos -> a
  | Neg -> -a
  | Not -> if a = 0 then 1 else 0

(* ---------------------------------------------------------------------- *)
(* 主入口：分析整个编译单元                                               *)
(* ---------------------------------------------------------------------- *)

let rec analyze (cu : comp_unit) : comp_unit =
  let st = ref empty in
  List.iter (fun item ->
    match item.node with
    | TopDecl d -> st := check_top_decl !st d
    | TopFunc f ->
      st := check_func_sig !st f;
      check_func_body !st f
  ) cu;
  (* 检查 main 函数 *)
  begin match lookup_func "main" !st with
    | Some (FuncInfo { ret_type = Int; param_names = [] }) -> ()
    | Some (FuncInfo { ret_type = Int; param_names = _ :: _ }) ->
        semant_error "main function must have no parameters"
    | Some (FuncInfo { ret_type = Void; _ }) ->
        semant_error "main function must return int"
    | None ->
        semant_error "missing main function"
    | Some _ ->
        semant_error "'main' must be declared as a function"
  end;
  cu

(* ---------------------------------------------------------------------- *)
(* 第一趟：顶层声明 & 函数签名                                            *)
(* ---------------------------------------------------------------------- *)

and check_top_decl (st : t) (d : decl) : t =
  match d.node with
  | ConstDecl { const_name = id; const_init = e } ->
    begin match lookup_current id st with
      | Some _ -> semant_error ~loc:d.loc ("redeclared identifier: " ^ id)
      | None ->
        let v = eval_const_expr st e in
        insert id (ConstInfo { value = v }) st
    end
  | VarDecl { var_name = id; var_init = e } ->
    begin match lookup_current id st with
      | Some _ -> semant_error ~loc:d.loc ("redeclared identifier: " ^ id)
      | None ->
        (* 当前 IR 只支持静态全局初始化；这里必须与 irgen.eval_global_init 保持同一约束，
           否则会出现 semant 放行、irgen 再崩溃的前后端契约断裂。 *)
        ignore (eval_const_expr st e);
        insert id (VarInfo { slot = 0 }) st
    end

and check_func_sig (st : t) (f : func_def) : t =
  let id = f.func_name in
  match lookup_func id st with
  | Some _ -> semant_error ~loc:f.func_loc ("redeclared function: " ^ id)
  | None ->
    insert id (FuncInfo {
      ret_type = f.func_ret;
      param_names = List.map (fun p -> p.param_name) f.func_params;
    }) st

(* ---------------------------------------------------------------------- *)
(* 第二趟：函数体检查                                                     *)
(* ---------------------------------------------------------------------- *)

and check_func_body (global_st : t) (f : func_def) : unit =
  let st = ref global_st in
  st := enter_scope !st;
  (* 检查参数名重复 *)
  let param_names = List.map (fun p -> p.param_name) f.func_params in
  if List.length param_names <> List.length (List.sort_uniq String.compare param_names) then
    semant_error ~loc:f.func_loc "duplicate parameter name";
  List.iteri (fun i p ->
    st := insert p.param_name (ParamInfo { slot = i }) !st
  ) f.func_params;
  check_block global_st st f.func_ret f.func_name 0 f.func_body;
  (* 返回值检查 *)
    if f.func_ret = Int && not (stmts_always_return !st f.func_body) then
    semant_error ~loc:f.func_loc
      ("function '" ^ f.func_name ^ "' may not return a value on all paths")

(* ---------------------------------------------------------------------- *)
(* 语句块检查                                                             *)
(* ---------------------------------------------------------------------- *)

and check_block (global_st : t) (st_ref : t ref) (fn_ret : typ) (fn_name : string)
    (loop_depth : int) (stmts : stmt list) : unit =
  st_ref := enter_scope !st_ref;
  List.iter (fun s -> check_stmt global_st st_ref fn_ret fn_name loop_depth s) stmts;
  st_ref := leave_scope !st_ref

(* ---------------------------------------------------------------------- *)
(* 语句检查 (loop_depth: 当前嵌套循环深度, 0 表示不在循环内)               *)
(* ---------------------------------------------------------------------- *)

and check_stmt (global_st : t) (st_ref : t ref) (fn_ret : typ) (fn_name : string) (loop_depth : int) (s : stmt) : unit =
  match s.node with
  | Block stmts ->
      check_block global_st st_ref fn_ret fn_name loop_depth stmts

  | Empty -> ()

  | ExprStmt e ->
      ignore (check_expr global_st !st_ref e)

  | Assign (id, e) ->
      let ty = check_expr global_st !st_ref e in
      if ty = Void then
        semant_error ~loc:s.loc "void expression used as assignment right-hand side";
      begin match lookup id !st_ref with
        | Some (ConstInfo _) -> semant_error ~loc:s.loc ("cannot assign to const: " ^ id)
        | Some (FuncInfo _) -> semant_error ~loc:s.loc ("cannot assign to function: " ^ id)
        | Some (VarInfo _ | ParamInfo _) -> ()
        | None -> semant_error ~loc:s.loc ("undeclared variable: " ^ id)
      end

  | DeclStmt d ->
      st_ref := check_local_decl !st_ref d

  | If (cond, then_s, else_s) ->
      let cond_ty = check_expr global_st !st_ref cond in
      if cond_ty = Void then semant_error ~loc:s.loc "void expression used as if condition";
      check_stmt global_st st_ref fn_ret fn_name loop_depth then_s;
      Option.iter (fun s' -> check_stmt global_st st_ref fn_ret fn_name loop_depth s') else_s

  | While (cond, body) ->
      let cond_ty = check_expr global_st !st_ref cond in
      if cond_ty = Void then semant_error ~loc:s.loc "void expression used as while condition";
      check_stmt global_st st_ref fn_ret fn_name (loop_depth + 1) body

  | Break ->
      if loop_depth = 0 then semant_error ~loc:s.loc "break outside of loop"

  | Continue ->
      if loop_depth = 0 then semant_error ~loc:s.loc "continue outside of loop"

  | Return e_opt ->
      begin match fn_ret, e_opt with
        | Int, None ->
            semant_error ~loc:s.loc ("function '" ^ fn_name ^ "' expects a return value")
        | Int, Some e ->
            let ty = check_expr global_st !st_ref e in
            if ty = Void then
              semant_error ~loc:s.loc "void expression used as return value"
        | Void, Some _ ->
            semant_error ~loc:s.loc ("void function '" ^ fn_name ^ "' should not return a value")
        | Void, None -> ()
      end

(* ---------------------------------------------------------------------- *)
(* 局部声明                                                               *)
(* ---------------------------------------------------------------------- *)

and check_local_decl (st : t) (d : decl) : t =
  match d.node with
  | ConstDecl { const_name = id; const_init = e } ->
    begin match lookup_current id st with
      | Some _ -> semant_error ~loc:d.loc ("redeclared identifier in local scope: " ^ id)
      | None ->
        let st' = insert id (VarInfo { slot = 0 }) st in
        let v = eval_const_expr st' e in
        insert id (ConstInfo { value = v }) st
    end
  | VarDecl { var_name = id; var_init = e } ->
    begin match lookup_current id st with
      | Some _ -> semant_error ~loc:d.loc ("redeclared identifier in local scope: " ^ id)
      | None ->
          (* 要求.md：局部声明从声明点开始生效，initializer 内部就应遮蔽外层同名符号。 *)
          let st' = insert id (VarInfo { slot = 0 }) st in
          let ty = check_expr st' st' e in
          if ty = Void then semant_error ~loc:d.loc "void expression used as variable initializer";
          st'
    end

(* ---------------------------------------------------------------------- *)
(* 表达式类型检查                                                         *)
(*   所有表达式返回 Int，除非是 void 函数调用返回 Void                      *)
(* ---------------------------------------------------------------------- *)

and check_expr (global_st : t) (st : t) (e : expr) : typ =
  match e.node with
  | Int _ -> Int

  | Var id ->
    begin match lookup id st with
      | Some (FuncInfo _) -> semant_error ~loc:e.loc ("function '" ^ id ^ "' used as value")
      | Some (VarInfo _ | ParamInfo _ | ConstInfo _) -> Int
      | None -> semant_error ~loc:e.loc ("undeclared identifier: " ^ id)
    end

  | Binary (e1, _op, e2) ->
    let t1 = check_expr global_st st e1 in
    let t2 = check_expr global_st st e2 in
    if t1 = Void || t2 = Void then
      semant_error ~loc:e.loc "void expression in binary operation";
    Int

  | Unary (_op, e') ->
    let t = check_expr global_st st e' in
    if t = Void then
      semant_error ~loc:e.loc "void expression in unary operation";
    Int

  | Call (id, args) ->
    let ret_type, param_names =
        match lookup id st with
      | Some (FuncInfo { ret_type; param_names }) -> ret_type, param_names
      | Some _ -> semant_error ~loc:e.loc ("identifier '" ^ id ^ "' is not a function")
      | None -> semant_error ~loc:e.loc ("undeclared function: " ^ id)
    in
    if List.length args <> List.length param_names then
      semant_error ~loc:e.loc (Printf.sprintf "function '%s' expects %d arguments, got %d"
        id (List.length param_names) (List.length args));
    List.iter (fun a ->
      let arg_ty = check_expr global_st st a in
      if arg_ty = Void then
        semant_error ~loc:a.loc "void expression used as function argument"
    ) args;
    ret_type

(* ---------------------------------------------------------------------- *)
  (* 返回路径检查                                                           *)
  (*   参考 Clang 基于 CFG 可达性的思路：            *)
  (*   - 顺序语句按“第一个不可继续执行的语句”截断；                           *)
  (*   - 对 if/else 使用可证明常量条件裁剪不可达分支；                       *)
  (*   - while 仍保持保守（默认认为可能从循环后继续执行）。                  *)
(* ---------------------------------------------------------------------- *)

  and try_eval_const_expr (st : t) (e : expr) : int option =
    match e.node with
    | Int n -> Some n
    | Var id ->
        begin
          match lookup id st with
          | Some (ConstInfo { value }) -> Some value
          | Some _ | None -> None
        end
    | Binary (e1, LAnd, e2) ->
        begin
          match try_eval_const_expr st e1 with
          | Some 0 -> Some 0
          | Some _ ->
              begin
                match try_eval_const_expr st e2 with
                | Some v2 -> Some (if v2 <> 0 then 1 else 0)
                | None -> None
              end
          | None -> None
        end
    | Binary (e1, LOr, e2) ->
        begin
          match try_eval_const_expr st e1 with
          | Some v1 when v1 <> 0 -> Some 1
          | Some _ ->
              begin
                match try_eval_const_expr st e2 with
                | Some v2 -> Some (if v2 <> 0 then 1 else 0)
                | None -> None
              end
          | None -> None
        end
    | Unary (op, e1) ->
        Option.map (eval_const_unop op) (try_eval_const_expr st e1)
    | Binary (e1, op, e2) ->
        begin
          match try_eval_const_expr st e1, try_eval_const_expr st e2 with
          | Some v1, Some v2 ->
              (try Some (eval_const_binop e.loc op v1 v2) with Failure _ -> None)
          | _ -> None
        end
    | Call _ ->
        None

  and flow_after_decl (st : t) (d : decl) : t =
    match d.node with
    | ConstDecl { const_name = id; const_init = e } ->
        begin
          match try_eval_const_expr st e with
          | Some value -> insert id (ConstInfo { value }) st
          | None -> insert id (VarInfo { slot = 0 }) st
        end
    | VarDecl { var_name = id; _ } ->
        insert id (VarInfo { slot = 0 }) st

  and flow_after_stmt (st : t) (s : stmt) : t =
    match s.node with
    | DeclStmt d -> flow_after_decl st d
    | Block _ | Empty | ExprStmt _ | Assign _ | If _ | While _ | Break | Continue | Return _ ->
        st

  and stmt_always_returns (st : t) (s : stmt) : bool =
  match s.node with
  | Return _ -> true
    | Block ss -> block_always_returns st ss
    | If (cond, s1, Some s2) ->
        begin
          match try_eval_const_expr st cond with
          | Some 0 -> stmt_always_returns st s2
          | Some _ -> stmt_always_returns st s1
          | None -> stmt_always_returns st s1 && stmt_always_returns st s2
        end
    | If (cond, s1, None) ->
        begin
          match try_eval_const_expr st cond with
          | Some 0 -> false
          | Some _ -> stmt_always_returns st s1
          | None -> false
        end
  | While _ -> false
  | Break | Continue -> false
  | Empty | ExprStmt _ | Assign _ | DeclStmt _ -> false

  and stmts_always_return (st : t) (stmts : stmt list) : bool =
    match stmts with
    | [] -> false
    | s :: rest ->
        if stmt_always_returns st s then true
        else stmts_always_return (flow_after_stmt st s) rest

  and block_always_returns (st : t) (stmts : stmt list) : bool =
    let st = enter_scope st in
    stmts_always_return st stmts
