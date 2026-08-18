(* ====================================================================== *)
(* ToyC 编译器 符号表                                                     *)
(*                                                                        *)
(* 作用域栈模型：每个 {} 推入一个新作用域，声明写入当前栈顶，              *)
(* 引用查找从栈顶向下搜索。                                               *)
(*                                                                        *)
(* 语义分析阶段：一边遍历 AST 一边填充符号表 + 校验；                     *)
(* IR 生成阶段：读符号表将变量名映射到 slot / 常量值。                     *)
(* ====================================================================== *)

open Common

(* ---------------------------------------------------------------------- *)
(* 符号信息                                                               *)
(* ---------------------------------------------------------------------- *)

type info =
  | VarInfo   of { slot : int }                     (* int x = ... *)
  | ConstInfo of { value : int }                    (* const int x = ... *)
  | ParamInfo of { slot : int }                     (* 函数形参 *)
  | FuncInfo  of { ret_type : typ; param_names : string list }  (* 函数定义 *)

(* ---------------------------------------------------------------------- *)
(* 作用域                                                                 *)
(* ---------------------------------------------------------------------- *)

module M = Map.Make(String)

type scope = info M.t

(* ---------------------------------------------------------------------- *)
(* 符号表                                                                 *)
(* ---------------------------------------------------------------------- *)

(* 作用域栈：head = 最内层当前作用域，tail = 外层 *)
type t = scope list

let empty : t = [ M.empty ]

(* 进入一个新的 {} 块 *)
let enter_scope (st : t) : t =
  M.empty :: st

(* 退出当前 {} 块 *)
let leave_scope (st : t) : t =
  match st with
  | [] -> failwith "Symtab.leave_scope: empty stack"
  | _ :: rest -> rest

(* 在当前作用域插入一个符号 *)
let insert (name : string) (i : info) (st : t) : t =
  match st with
  | [] -> failwith "Symtab.insert: empty stack"
  | cur :: outer ->
    let cur' = M.add name i cur in
    cur' :: outer

(* 仅查当前作用域，允许内层屏蔽外层 *)
let lookup_current (name : string) (st : t) : info option =
  match st with
  | [] -> None
  | cur :: _ -> M.find_opt name cur

(* 从内向外查找符号 *)
let rec lookup (name : string) (st : t) : info option =
  match st with
  | [] -> None
  | cur :: outer ->
    match M.find_opt name cur with
    | Some _ as res -> res
    | None -> lookup name outer

(* 查找函数（只在最外层作用域，即全局作用域） *)
let lookup_func (name : string) (st : t) : info option =
  match List.rev st with
  | global :: _ -> M.find_opt name global
  | [] -> None
