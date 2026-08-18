(* ToyC 优化 — 乘除简化
   1. 2的幂乘法 → 移位: Mul(x, 2^k) → Shl(x, k)
   2. 常量乘法拆移位+加法: Mul(x, C) → Σ Shl(x, bit_i)
   3. 2的幂除法 → 算术右移 (含负数修正): Div(x, 2^k) → AShr(x+bias, k) *)

open Ir_types
open Common

(* ---- 工具函数 ---------------------------------------------------------- *)

let is_power_of_two n = n > 0 && n land (n - 1) = 0

let log2 n =
  let rec loop acc m =
    if m = 1 then acc else loop (acc + 1) (m / 2)
  in
  if is_power_of_two n then Some (loop 0 n) else None

let popcount n =
  let rec loop acc m =
    if m = 0 then acc
    else loop (acc + (m land 1)) (m lsr 1)
  in
  loop 0 n

(* 返回 C 中置位的 bit 位置列表, MSB first *)
let bits_of_constant n =
  let rec loop pos m acc =
    if m = 0 then acc
    else if m land 1 = 1 then loop (pos + 1) (m lsr 1) (pos :: acc)
    else loop (pos + 1) (m lsr 1) acc
  in
  loop 0 n []

(* ---- 优化 1: 2的幂乘法 → 移位 ---------------------------------------- *)

(* Mul(x, 2^k) 或 Mul(2^k, x) → Shl(x, k) *)
let try_pow2_mul = function
  | Binop { dst; op = Mul; lhs; rhs = Imm n } ->
    (match log2 n with Some k -> Some (Shl { dst; lhs; rhs = Imm k }) | None -> None)
  | Binop { dst; op = Mul; lhs = Imm n; rhs } ->
    (match log2 n with Some k -> Some (Shl { dst; lhs = rhs; rhs = Imm k }) | None -> None)
  | _ -> None

(* ---- 优化 2: 常量乘法拆移位+加法 --------------------------------------- *)

(* Mul(x, C) 其中 C 有 2~4 个置位 bit → 拆成移位+加法链 *)
let try_decompose_mul = function
  | Binop { dst; op = Mul; lhs; rhs = Imm n }
    when n > 1 && not (is_power_of_two n) && popcount n <= 4 ->
    Some (lhs, n, dst)
  | Binop { dst; op = Mul; lhs = Imm n; rhs }
    when n > 1 && not (is_power_of_two n) && popcount n <= 4 ->
    Some (rhs, n, dst)
  | _ -> None

let expand_mul_const fresh x c dst =
  let bits = bits_of_constant c in
  let instrs_rev, terms_rev =
    List.fold_left (fun (instrs, terms) b ->
      if b = 0 then (instrs, x :: terms)
      else
        let t = fresh () in
        (Shl { dst = t; lhs = x; rhs = Imm b } :: instrs, VReg t :: terms)
    ) ([], []) bits
  in
  let instrs = List.rev instrs_rev in
  let terms = List.rev terms_rev in
  match terms with
  | [] -> [Copy { dst; src = Imm 0 }]
  | [single] -> instrs @ [Copy { dst; src = single }]
  | first :: rest ->
    let rec emit_adds acc = function
      | [] -> []
      | [last] -> [Binop { dst; op = Add; lhs = acc; rhs = last }]
      | term :: rest ->
        let t = fresh () in
        Binop { dst = t; op = Add; lhs = acc; rhs = term }
        :: emit_adds (VReg t) rest
    in
    instrs @ emit_adds first rest

(* ---- 优化 3: 2的幂除法 → 算术右移 (含负数修正) ------------------------- *)

(* Div(x, 2^k) →
     sign  = AShr(x, 31)
     bias  = And(sign, 2^k-1)
     tmp   = Add(x, bias)
     dst   = AShr(tmp, k) *)
let try_pow2_div = function
  | Binop { dst; op = Div; lhs; rhs = Imm n } when n > 1 && is_power_of_two n ->
    let k = Option.get (log2 n) in
    if k <= 0 || k > 30 then None
    else Some (lhs, k, dst)
  | _ -> None

let expand_div_const fresh x k dst =
  let sign_v = fresh () in
  let bias_v = fresh () in
  let biased = fresh () in
  let mask = (1 lsl k) - 1 in
  [ AShr { dst = sign_v; lhs = x; rhs = Imm 31 };
    And  { dst = bias_v; lhs = VReg sign_v; rhs = Imm mask };
    Binop { dst = biased; op = Add; lhs = x; rhs = VReg bias_v };
    AShr { dst; lhs = VReg biased; rhs = Imm k } ]

(* ---- 主 pass ---------------------------------------------------------- *)

let run_on_func (f : func) : func =
  let next_vreg = ref (f.f_max_vreg + 1) in
  let fresh () = let r = !next_vreg in incr next_vreg; r in
  let process_instr instr =
    match try_pow2_mul instr with
    | Some new_instr -> [new_instr]
    | None ->
      match try_decompose_mul instr with
      | Some (x, c, dst) -> expand_mul_const fresh x c dst
      | None ->
        match try_pow2_div instr with
        | Some (x, k, dst) -> expand_div_const fresh x k dst
        | None -> [instr]
  in
  let new_blocks = List.map (fun (lbl, bb) ->
    let new_instrs = List.concat_map process_instr bb.bb_instrs in
    (lbl, { bb with bb_instrs = new_instrs })
  ) f.f_blocks in
  { f with f_blocks = new_blocks; f_max_vreg = !next_vreg - 1 }

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
