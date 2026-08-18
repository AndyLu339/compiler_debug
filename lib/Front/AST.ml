(* ====================================================================== *)
(* ToyC 语言 AST 定义                                                    *)
(* ====================================================================== *)

open Common

(* Expr              → LOrExpr                                                   *)
(* LOrExpr           → LAndExpr | LOrExpr "||" LAndExpr                          *)
(* LAndExpr          → RelExpr | LAndExpr "&&" RelExpr                           *)
(* RelExpr           → AddExpr | RelExpr ("<" | ">" | "<=" | ">=" | "==" | "!=") AddExpr *)
(* AddExpr           → MulExpr | AddExpr ("+" | "-") MulExpr                     *)
(* MulExpr           → UnaryExpr | MulExpr ("*" | "/" | "%") UnaryExpr           *)
(* UnaryExpr         → PrimaryExpr | ("+" | "-" | "!") UnaryExpr                 *)
(* PrimaryExpr       → ID | NUMBER | "(" Expr ")" | ID "(" (Expr ("," Expr)* )? ")" *)
type expr_node =
  | Var    of string
  | Int    of int
  | Binary of expr * binary_op * expr
  | Unary  of unary_op * expr
  | Call   of string * expr list

and expr = expr_node located

(* ---------------------------------------------------------------------- *)
(* 参数                                                                   *)
(* ---------------------------------------------------------------------- *)

(* Param             → "int" ID *)
type param = {
  param_name : string;
}

(* ---------------------------------------------------------------------- *)
(* 语句与声明（相互递归：Stmt 可包含 Decl）                                *)
(* ---------------------------------------------------------------------- *)

type stmt_node =
  | Block    of block
  | Empty
  | ExprStmt of expr
  | Assign   of string * expr
  | DeclStmt of decl
  | If       of expr * stmt * stmt option
  | While    of expr * stmt
  | Break
  | Continue
  | Return   of expr option

and stmt = stmt_node located

and decl_node =
  | ConstDecl of const_decl
  | VarDecl   of var_decl

and decl = decl_node located

(* ConstDecl         → "const" "int" ID "=" Expr ";" *)
and const_decl = {
  const_name : string;
  const_init : expr;
}

(* VarDecl           → "int" ID "=" Expr ";" *)
and var_decl = {
  var_name : string;
  var_init : expr;
}

(* Block             → "{" Stmt* "}" *)
and block = stmt list

(* ---------------------------------------------------------------------- *)
(* 函数定义                                                               *)
(* ---------------------------------------------------------------------- *)

(* FuncDef           → ("int" | "void") ID "(" (Param ("," Param)* )? ")" Block *)
type func_def = {
  func_ret    : typ;
  func_name   : string;
  func_params : param list;
  func_body   : block;
  func_loc    : loc;
}

(* ---------------------------------------------------------------------- *)
(* 编译单元                                                               *)
(* ---------------------------------------------------------------------- *)

(* CompUnit          → (Decl | FuncDef)+ *)
type comp_unit_item_node =
  | TopDecl of decl
  | TopFunc of func_def

type comp_unit_item = comp_unit_item_node located

type comp_unit = comp_unit_item list
