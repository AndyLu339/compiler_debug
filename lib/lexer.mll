(* ToyC 词法分析器 (ocamllex) *)

{
open Parser

let lexer_error lexbuf msg =
  let p = Lexing.lexeme_start_p lexbuf in
  failwith (Printf.sprintf "Lexical error at %d:%d: %s"
    p.Lexing.pos_lnum (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1) msg)
}

let whitespace = [' ' '\t' '\r']

rule token = parse
  | whitespace+         { token lexbuf }
  | '\n'                { Lexing.new_line lexbuf; token lexbuf }

  (* 注释 *)
  | "//" [^ '\n']* '\n'? { Lexing.new_line lexbuf; token lexbuf }
  | "/*"                { comment lexbuf; token lexbuf }

  (* 关键字 *)
  | "int"      { INT }
  | "void"     { VOID }
  | "const"    { CONST }
  | "if"       { IF }
  | "else"     { ELSE }
  | "while"    { WHILE }
  | "break"    { BREAK }
  | "continue" { CONTINUE }
  | "return"   { RETURN }

  (* 多字符运算符 *)
  | "==" { EQEQ }
  | "!=" { NE }
  | "<=" { LE }
  | ">=" { GE }
  | "&&" { LAND }
  | "||" { LOR }

  (* 单字符运算符与分隔符 *)
  | '+' { PLUS }  | '-' { MINUS }  | '*' { TIMES }
  | '/' { DIVIDE }  | '%' { MOD }    | '!' { NOT }
  | '=' { EQ }      | '<' { LT }     | '>' { GT }
  | '(' { LPAREN }  | ')' { RPAREN }
  | '{' { LBRACE }  | '}' { RBRACE }
  | ';' { SEMICOLON }  | ',' { COMMA }

  (* 整数常量 *)
  | '0'
  | ['1'-'9'] ['0'-'9']* as num
    { NUMBER (int_of_string num) }

  (* 标识符 *)
  | ['_' 'A'-'Z' 'a'-'z'] ['_' 'A'-'Z' 'a'-'z' '0'-'9']* as id
    { ID id }

  | eof { EOF }

  | _ as c
    { lexer_error lexbuf (Printf.sprintf "unexpected character '%c'" c) }

and comment = parse
  | '\n'     { Lexing.new_line lexbuf; comment lexbuf }
  | "*/"     { () }
  | eof      { lexer_error lexbuf "unclosed comment" }
  | _        { comment lexbuf }
