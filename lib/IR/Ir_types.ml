(* ToyC IR — 类型定义 *)

open Common

(* 类型 *)
type ir_type = I32 | I1 | Void

(* SSA 值 *)
type value =
  | VReg of int
  | Imm of int
  | Global of string

(* 基本块标号 *)
type label = int

(* 比较条件 *)
type icmp_cond = IEq | INe | ISlt | ISle | ISgt | ISge

(* 非终结指令 *)
type instr =
  | Alloca of { dst : int; ty : ir_type }
  | Load   of { dst : int; ptr : value }
  | Store  of { val_ : value; ptr : value }
  | Binop  of { dst : int; op : binary_op; lhs : value; rhs : value }
  | Icmp   of { dst : int; cond : icmp_cond; lhs : value; rhs : value }
  | Call   of { dst : int option; fn : string; args : value list }
  | Phi    of { dst : int; incoming : (value * label) list }
  | Shl    of { dst : int; lhs : value; rhs : value }
  | AShr   of { dst : int; lhs : value; rhs : value }
  | And    of { dst : int; lhs : value; rhs : value }
  | Zext   of { dst : int; src : value }
  | Copy   of { dst : int; src : value }

(* 终结指令 *)
type terminator =
  | Ret  of value option
  | Br   of value * label * label
  | Jump of label

(* 基本块: 直线指令序列 + 唯一终结指令 *)
type basic_block = {
  bb_label  : label;
  bb_instrs : instr list;
  bb_term   : terminator;
}

(* 函数 *)
type func = {
  f_name     : string;
  f_ret      : typ;
  f_params   : (string * int) list;   (* 形参名 * vreg *)
  f_blocks   : (label * basic_block) list;
  f_entry    : label;
  f_max_vreg : int;
  f_max_label : int;
}

(* 全局 *)
type global =
  | GVar   of { name : string; init : int }
  | GConst of { name : string; value : int }

(* 模块 *)
type module_ = {
  m_globals : global list;
  m_funcs   : (string * func) list;
}

(* 提取指令的目的 vreg *)
let instr_dst = function
  | Alloca { dst; _ }  -> Some dst
  | Load   { dst; _ }  -> Some dst
  | Binop  { dst; _ }  -> Some dst
  | Icmp   { dst; _ }  -> Some dst
  | Call   { dst; _ }  -> dst
  | Phi    { dst; _ }  -> Some dst
  | Shl    { dst; _ }  -> Some dst
  | AShr   { dst; _ }  -> Some dst
  | And    { dst; _ }  -> Some dst
  | Zext   { dst; _ }  -> Some dst
  | Copy   { dst; _ }  -> Some dst
  | Store _            -> None

(* 提取指令使用的 operand *)
let instr_uses = function
  | Alloca _               -> []
  | Load   { ptr; _ }      -> [ ptr ]
  | Store  { val_; ptr }   -> [ val_; ptr ]
  | Binop  { lhs; rhs; _ } -> [ lhs; rhs ]
  | Icmp   { lhs; rhs; _ } -> [ lhs; rhs ]
  | Call   { args; _ }     -> args
  | Phi    { incoming; _ } -> List.map fst incoming
  | Shl    { lhs; rhs; _ } -> [ lhs; rhs ]
  | AShr   { lhs; rhs; _ } -> [ lhs; rhs ]
  | And    { lhs; rhs; _ } -> [ lhs; rhs ]
  | Zext   { src; _ }      -> [ src ]
  | Copy   { src; _ }      -> [ src ]

(* 提取终结指令使用的 operand *)
let terminator_uses = function
  | Ret (Some v) -> [ v ]
  | Ret None     -> []
  | Br (cond, _, _) -> [ cond ]
  | Jump _       -> []

(* 基本块内所有 operand *)
let all_uses_of_bb bb =
  List.concat_map instr_uses bb.bb_instrs @ terminator_uses bb.bb_term
