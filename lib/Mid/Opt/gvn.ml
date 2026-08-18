(* ToyC 优化 — 全局值编号 (GVN)
   沿支配树做值编号, 消除跨块冗余计算; 附带 sound 的 phi 同余.
   注: 完整 PRE (部分冗余消除) 未实现, 见 docs/LLVM优化管线差距分析.md 3.1 *)

open Ir_types
open Common

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

(* 值编号: 每个值的同余类表示 *)
type vn =
  | VNImm of int
  | VNGlobal of string
  | VNReg of int          (* 恒等值: 参数 / 不可编号指令结果 / 未合并的 phi *)
  | VNExpr of expr_key    (* 纯表达式 *)

and expr_key =
  | KBinop of binary_op * vn * vn
  | KIcmp of icmp_cond * vn * vn
  | KShl of vn * vn
  | KAShr of vn * vn
  | KAnd of vn * vn
  | KZext of vn

module ExprMap = Map.Make (struct type t = expr_key let compare = compare end)

(* ---- 值替换 (与 algebraic/cse 相同的 apply_repl 模式) ------------------- *)

let rec resolve_value (repl : value IntMap.t) (v : value) : value =
  match v with
  | VReg r ->
      (match IntMap.find_opt r repl with
       | Some v' -> resolve_value repl v'
       | None -> v)
  | Imm _ | Global _ -> v

let apply_repl (f : func) (repl : value IntMap.t) : func =
  let rv = resolve_value repl in
  let ri instr = match instr with
    | Alloca _ -> instr
    | Load l   -> Load { l with ptr = rv l.ptr }
    | Store s  -> Store { val_ = rv s.val_; ptr = rv s.ptr }
    | Binop b  -> Binop { b with lhs = rv b.lhs; rhs = rv b.rhs }
    | Icmp c   -> Icmp { c with lhs = rv c.lhs; rhs = rv c.rhs }
    | Call c   -> Call { c with args = List.map rv c.args }
    | Phi p    -> Phi { p with incoming = List.map (fun (v, l) -> (rv v, l)) p.incoming }
    | Shl s    -> Shl { s with lhs = rv s.lhs; rhs = rv s.rhs }
    | AShr s   -> AShr { s with lhs = rv s.lhs; rhs = rv s.rhs }
    | And a    -> And { a with lhs = rv a.lhs; rhs = rv a.rhs }
    | Zext z   -> Zext { z with src = rv z.src }
    | Copy c   -> Copy { c with src = rv c.src }
  in
  let rt = function
    | Ret (Some v)    -> Ret (Some (rv v))
    | Ret None        -> Ret None
    | Br (cond, t, f) -> Br (rv cond, t, f)
    | Jump _ as j     -> j
  in
  let new_blocks = List.map (fun (lbl, bb) ->
    let new_instrs = List.filter_map (fun instr ->
      match instr_dst instr with
      | Some dst when IntMap.mem dst repl -> None
      | _ -> Some (ri instr)
    ) bb.bb_instrs in
    (lbl, { bb with bb_instrs = new_instrs; bb_term = rt bb.bb_term })
  ) f.f_blocks in
  { f with f_blocks = new_blocks }

(* ---- 单函数 ------------------------------------------------------------ *)

let run_on_func (f : func) : func =
  let dom = Dominance.analyze f in
  let block_map =
    List.fold_left (fun acc (lbl, bb) -> IntMap.add lbl bb acc) IntMap.empty f.f_blocks
  in

  let vn_of = ref IntMap.empty in       (* vreg -> vn *)
  let repl = ref IntMap.empty in        (* vreg -> 替换值 (待删除的冗余定义) *)
  let def_block = ref IntMap.empty in   (* vreg -> 定义所在块 *)

  List.iter (fun (_, r) ->
    vn_of := IntMap.add r (VNReg r) !vn_of;
    def_block := IntMap.add r f.f_entry !def_block
  ) f.f_params;

  let vn_value (v : value) : vn =
    match v with
    | Imm n -> VNImm n
    | Global g -> VNGlobal g
    | VReg r -> (match IntMap.find_opt r !vn_of with Some v -> v | None -> VNReg r)
  in

  let norm2 (a : vn) (b : vn) = if compare a b <= 0 then (a, b) else (b, a) in

  let expr_key_of instr : expr_key option =
    match instr with
    | Binop { op; lhs; rhs; _ } ->
        let a, b = match op with
          | Add | Mul | Eq | Ne -> norm2 (vn_value lhs) (vn_value rhs)
          | _ -> (vn_value lhs, vn_value rhs)
        in
        Some (KBinop (op, a, b))
    | Icmp { cond; lhs; rhs; _ } ->
        let a, b = match cond with
          | IEq | INe -> norm2 (vn_value lhs) (vn_value rhs)
          | _ -> (vn_value lhs, vn_value rhs)
        in
        Some (KIcmp (cond, a, b))
    | Shl { lhs; rhs; _ } -> Some (KShl (vn_value lhs, vn_value rhs))
    | AShr { lhs; rhs; _ } -> Some (KAShr (vn_value lhs, vn_value rhs))
    | And { lhs; rhs; _ } -> Some (KAnd (vn_value lhs, vn_value rhs))
    | Zext { src; _ } -> Some (KZext (vn_value src))
    | _ -> None
  in

  (* 沿支配树 DFS: env 线程化, 只沿支配者链传播可用表达式, 保证替换 sound *)
  let rec dfs lbl (env : int ExprMap.t) =
    let bb = IntMap.find lbl block_map in
    let env_ref = ref env in
    List.iter (fun instr ->
      match instr with
      | Phi { dst; _ } ->
          (* phi 留给后面的同余 fixpoint 处理, 此处只登记恒等 vn *)
          def_block := IntMap.add dst lbl !def_block;
          vn_of := IntMap.add dst (VNReg dst) !vn_of
      | _ ->
          (match expr_key_of instr, instr_dst instr with
           | Some k, Some dst ->
               def_block := IntMap.add dst lbl !def_block;
               (match ExprMap.find_opt k !env_ref with
                | Some prev ->
                    repl := IntMap.add dst (VReg prev) !repl;
                    vn_of := IntMap.add dst (vn_value (VReg prev)) !vn_of
                | None ->
                    env_ref := ExprMap.add k dst !env_ref;
                    vn_of := IntMap.add dst (VNExpr k) !vn_of)
           | None, Some dst ->
               def_block := IntMap.add dst lbl !def_block;
               (match instr with
                | Copy { src; _ } ->
                    repl := IntMap.add dst src !repl;
                    vn_of := IntMap.add dst (vn_value src) !vn_of
                | _ ->
                    vn_of := IntMap.add dst (VNReg dst) !vn_of)
           | Some _, None -> ()   (* 不可能: expr_key_of 只对带 dst 的指令返回 Some *)
           | None, None -> ())
    ) bb.bb_instrs;
    match IntMap.find_opt lbl dom.Dominance.children with
    | Some children -> IntSet.iter (fun child -> dfs child !env_ref) children
    | None -> ()
  in

  dfs f.f_entry ExprMap.empty;

  (* ---- phi 同余 (sound): 所有 incoming 值同 vn, 且该值在 phi 块可用 ----
     Imm/Global 恒可用; VReg r 需 def_block[r] 严格支配 phi 所在块.
     VNExpr 不处理 (那是 PRE 的活, 需要插入新计算, 这里不做). *)
  let vn_to_value (v : vn) : value option =
    match v with
    | VNImm n -> Some (Imm n)
    | VNGlobal g -> Some (Global g)
    | VNReg r -> Some (VReg r)
    | VNExpr _ -> None
  in

  let rec phi_fixpoint () =
    let changed = ref false in
    List.iter (fun (lbl, bb) ->
      List.iter (fun instr ->
        match instr with
        | Phi { dst; incoming } ->
            (match incoming with
             | [] -> ()
             | (v0, _) :: rest ->
                 let c = vn_value v0 in
                 if List.for_all (fun (v, _) -> vn_value v = c) rest then begin
                   let available =
                     match c with
                     | VNImm _ | VNGlobal _ -> true
                     | VNReg r ->
                         (match IntMap.find_opt r !def_block with
                          | Some b -> b <> lbl && IntSet.mem b (IntMap.find lbl dom.Dominance.doms)
                          | None -> false)
                     | VNExpr _ -> false
                   in
                   if available then
                     match vn_to_value c with
                     | Some target when IntMap.find_opt dst !repl = None ->
                         repl := IntMap.add dst target !repl;
                         vn_of := IntMap.add dst c !vn_of;
                         changed := true
                     | _ -> ()
                 end)
        | _ -> ()
      ) bb.bb_instrs
    ) f.f_blocks;
    if !changed then phi_fixpoint ()
  in

  phi_fixpoint ();

  if IntMap.is_empty !repl then f else apply_repl f !repl

(* ---- 入口 -------------------------------------------------------------- *)

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
