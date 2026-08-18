(* ====================================================================== *)
(* ToyC 编译器公共定义                                                    *)
(* AST 与 CFG 共享的类型                                                  *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* 类型                                                                   *)
(* ---------------------------------------------------------------------- *)

(* "int" | "void" *)
type typ = Int | Void

(* ---------------------------------------------------------------------- *)
(* 运算符                                                                 *)
(* ---------------------------------------------------------------------- *)

(* 二元运算符 *)
type binary_op =
  | LOr   (* || *)
  | LAnd  (* && *)
  | Eq    (* == *)
  | Ne    (* != *)
  | Lt    (* <  *)
  | Gt    (* >  *)
  | Le    (* <= *)
  | Ge    (* >= *)
  | Add   (* +  *)
  | Sub   (* -  *)
  | Mul   (* *  *)
  | Div   (* /  *)
  | Mod   (* %  *)

(* 一元运算符 *)
type unary_op =
  | Pos  (* + *)
  | Neg  (* - *)
  | Not  (* ! *)

(* ---------------------------------------------------------------------- *)
(* 源码位置                                                               *)
(* ---------------------------------------------------------------------- *)

type loc = Lexing.position * Lexing.position

let string_of_loc ((sp, ep) : loc) : string =
  let line = sp.Lexing.pos_lnum in
  let col1 = sp.Lexing.pos_cnum - sp.Lexing.pos_bol + 1 in
  let col2 = ep.Lexing.pos_cnum - ep.Lexing.pos_bol + 1 in
  if line = ep.Lexing.pos_lnum then
    Printf.sprintf "%d:%d-%d" line col1 col2
  else
    Printf.sprintf "%d:%d-%d:%d" line col1 ep.Lexing.pos_lnum col2

(* 带位置的 AST 节点包装 *)
type 'a located = {
  node : 'a;
  loc  : loc;
}
