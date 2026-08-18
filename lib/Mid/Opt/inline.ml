(* ToyC 优化 — 函数内联
   将小叶子函数体展开到调用处, 消除 call/ret 开销 *)

open Ir_types

module IntMap = Map.Make (Int)

(* ---- 启发式参数 -------------------------------------------------------- *)

(* 参考 LLVM InlineCost 的思路，内联决策更接近“cost vs threshold”，
   而不是只看“最多调用几次”这种硬门槛。 *)
let base_inline_threshold = 15
let max_inline_total_growth = 64

(* ---- 辅助: 函数分析 ---------------------------------------------------- *)

let count_instrs (f : func) =
  List.fold_left (fun acc (_, bb) -> acc + List.length bb.bb_instrs) 0 f.f_blocks

let count_blocks (f : func) =
  List.length f.f_blocks

let count_cond_branches (f : func) =
  List.fold_left (fun acc (_, bb) ->
    match bb.bb_term with
    | Br _ -> acc + 1
    | Jump _ | Ret _ -> acc
  ) 0 f.f_blocks

let is_leaf (f : func) =
  not (List.exists (fun (_, bb) ->
    List.exists (function Call _ -> true | _ -> false) bb.bb_instrs
  ) f.f_blocks)

let is_recursive (f : func) =
  List.exists (fun (_, bb) ->
    List.exists (function Call { fn; _ } -> fn = f.f_name | _ -> false) bb.bb_instrs
  ) f.f_blocks

(* 统计 f_name 在整个模块中被调用的次数 *)
let count_call_sites (m : module_) (target : string) =
  List.fold_left (fun acc (_, f) ->
    List.fold_left (fun acc (_, bb) ->
      List.fold_left (fun acc -> function
        | Call { fn; _ } when fn = target -> acc + 1
        | _ -> acc
      ) acc bb.bb_instrs
    ) acc f.f_blocks
  ) 0 m.m_funcs

let count_const_args (args : value list) =
  List.fold_left (fun acc -> function
    | Imm _ -> acc + 1
    | VReg _ | Global _ -> acc
  ) 0 args

let inline_cost (f : func) =
  (* terminator/CFG 越复杂，真实展开代价越高；这里给分支和额外块加成本。 *)
  count_instrs f + count_cond_branches f * 2 + max 0 (count_blocks f - 1)

let inline_threshold_for_call (f : func) (args : value list) =
  let const_args = count_const_args args in
  (* 参考 LLVM CallAnalyzer 会把调用点实参带入分析：
     常量实参越多，越可能触发比较/分支折叠，因此提高阈值。 *)
  base_inline_threshold
  + const_args * 2
  + if const_args > 0 then count_cond_branches f * 3 else 0

let should_inline_call (m : module_) (f : func) (args : value list) =
  let call_sites = count_call_sites m f.f_name in
  let cost = inline_cost f in
  let threshold = inline_threshold_for_call f args in
  f.f_name <> "main"
  && not (is_recursive f)
  && is_leaf f
  && cost <= threshold
  && cost * call_sites <= max_inline_total_growth

(* ---- value / label 重编号 ---------------------------------------------- *)

let remap_value (off_v : int) (v : value) : value = match v with
  | VReg r -> VReg (r + off_v)
  | Imm _ | Global _ -> v

let remap_instr (off_v : int) (off_l : int) (i : instr) : instr =
  let rv = remap_value off_v in
  match i with
  | Alloca { dst; ty } -> Alloca { dst = dst + off_v; ty }
  | Load { dst; ptr }  -> Load { dst = dst + off_v; ptr = rv ptr }
  | Store { val_; ptr } -> Store { val_ = rv val_; ptr = rv ptr }
  | Binop { dst; op; lhs; rhs } ->
      Binop { dst = dst + off_v; op; lhs = rv lhs; rhs = rv rhs }
  | Icmp { dst; cond; lhs; rhs } ->
      Icmp { dst = dst + off_v; cond; lhs = rv lhs; rhs = rv rhs }
  | Call { dst; fn; args } ->
      Call { dst = Option.map ((+) off_v) dst; fn; args = List.map rv args }
  | Phi { dst; incoming } ->
      Phi { dst = dst + off_v;
            incoming = List.map (fun (v, lbl) -> (rv v, lbl + off_l)) incoming }
  | Shl { dst; lhs; rhs } -> Shl { dst = dst + off_v; lhs = rv lhs; rhs = rv rhs }
  | AShr { dst; lhs; rhs } -> AShr { dst = dst + off_v; lhs = rv lhs; rhs = rv rhs }
  | And { dst; lhs; rhs } -> And { dst = dst + off_v; lhs = rv lhs; rhs = rv rhs }
  | Zext { dst; src } -> Zext { dst = dst + off_v; src = rv src }
  | Copy { dst; src } -> Copy { dst = dst + off_v; src = rv src }

let remap_term (off_v : int) (off_l : int) (t : terminator) : terminator =
  let rv = remap_value off_v in
  match t with
  | Ret v -> Ret (Option.map rv v)
  | Br (cond, t_lbl, f_lbl) -> Br (rv cond, t_lbl + off_l, f_lbl + off_l)
  | Jump l -> Jump (l + off_l)

(* ---- 在 caller 中的一个 call site 处内联 callee ----------------------- *)

(* call_site = (caller_func_name, call_block_label, call_instr_index)
   返回更新后的函数列表 *)
let inline_one_call (funcs : (string * func) list)
      (caller_name : string) (call_blk : label) (call_idx : int)
      (callee_name : string) : (string * func) list =
  let caller = List.assoc caller_name funcs in
  let callee = List.assoc callee_name funcs in

  let off_v = caller.f_max_vreg + 1 in
  let off_l = caller.f_max_label + 1 in
  let cont_lbl = off_l + callee.f_max_label + 1 in

  (* 拆分基本块 *)
  let bmap = List.fold_left (fun m (l, bb) -> IntMap.add l bb m)
      IntMap.empty caller.f_blocks in
  let bb = IntMap.find call_blk bmap in
  let call_instr = List.nth bb.bb_instrs call_idx in
  let call_args = match call_instr with
    | Call { args; _ } -> args | _ -> assert false in
  let call_dst = instr_dst call_instr in

  let prefix_instrs = List.filteri (fun i _ -> i < call_idx) bb.bb_instrs in
  let suffix_instrs = List.filteri (fun i _ -> i > call_idx) bb.bb_instrs in

  (* 返回值 SSA 合并: callee 重编号后 vreg 占用 [off_v, off_v+callee.f_max_vreg],
     多 return 时需要在其后分配临时 vreg 承接每个 return 值 *)
  let next_vreg = ref (off_v + callee.f_max_vreg + 1) in
  let fresh () = let r = !next_vreg in incr next_vreg; r in

  (* 收集所有带返回值的 return 块 (原始 label * callee 返回值) *)
  let ret_specs =
    match call_dst with
    | None -> []
    | Some _ ->
        List.filter_map (fun (lbl, cbb) ->
          match cbb.bb_term with
          | Ret (Some v) -> Some (lbl, v)
          | _ -> None
        ) callee.f_blocks
  in
  (* 多个 return 块会向同一个 call_dst 写值, 违反 SSA 单一定义;
     给每个 return 块分配独立临时 vreg, 再在接续块用 φ 合并 *)
  let multi_ret = List.length ret_specs > 1 in
  let ret_tmp =
    if multi_ret then
      List.fold_left (fun m (lbl, _) -> IntMap.add lbl (fresh ()) m)
        IntMap.empty ret_specs
    else IntMap.empty
  in

  (* 参数传递: Copy arg → remapped param *)
  let arg_copies = List.mapi (fun i (_, pv) ->
    let arg = List.nth call_args i in
    Copy { dst = pv + off_v; src = arg }
  ) callee.f_params in

  (* 新前缀块 *)
  let prefix_bb = { bb with
    bb_instrs = prefix_instrs @ arg_copies;
    bb_term = Jump (callee.f_entry + off_l) } in

  (* 新接续块: 多 return 时在块头插入 φ 把各临时值合并回 call_dst *)
  let cont_phi =
    if multi_ret then
      match call_dst with
      | Some dst ->
          let incoming = List.map (fun (lbl, _) ->
            (VReg (IntMap.find lbl ret_tmp), lbl + off_l)
          ) ret_specs in
          [Phi { dst; incoming }]
      | None -> []
    else [] in
  let cont_bb = {
    bb_label = cont_lbl;
    bb_instrs = cont_phi @ suffix_instrs;
    bb_term = bb.bb_term } in

  (* 重编号 callee 块; Ret 改为 Jump cont_lbl + 返回值 Copy *)
  let callee_blocks = List.map (fun (lbl, cbb) ->
    let cbb = {
      bb_label = cbb.bb_label + off_l;
      bb_instrs = List.map (remap_instr off_v off_l) cbb.bb_instrs;
      bb_term = remap_term off_v off_l cbb.bb_term;
    } in
    let cbb = match cbb.bb_term with
      | Ret None ->
          { cbb with bb_term = Jump cont_lbl }
      | Ret (Some v) ->
          let copy = match call_dst with
            | Some dst ->
                (* 多 return 时写到临时 vreg, 单 return 时直接写 call_dst *)
                let copy_dst = if multi_ret then IntMap.find lbl ret_tmp else dst in
                [Copy { dst = copy_dst; src = v }]
            | None -> [] in
          { cbb with bb_instrs = cbb.bb_instrs @ copy; bb_term = Jump cont_lbl }
      | _ -> cbb
    in
    (cbb.bb_label, cbb)
  ) callee.f_blocks in

  (* 更新 phi: 原 call_blk 被分割, successor 中引用 call_blk 的要改为 cont_lbl *)
  let bmap = IntMap.add call_blk prefix_bb bmap in
  let bmap = ref (IntMap.add cont_lbl cont_bb bmap) in
  List.iter (fun (lbl, cbb) -> bmap := IntMap.add lbl cbb !bmap) callee_blocks;
  let bmap = IntMap.map (fun bb ->
    { bb with bb_instrs = List.map (fun instr ->
      match instr with
      | Phi { dst; incoming } ->
          Phi { dst; incoming = List.map (fun (v, lbl) ->
            if lbl = call_blk then (v, cont_lbl) else (v, lbl)
          ) incoming }
      | _ -> instr
    ) bb.bb_instrs }
  ) !bmap in

  (* 重建成有序列表 *)
  let new_blocks = IntMap.bindings bmap
    |> List.sort (fun (a,_) (b,_) -> compare a b) in
  let new_caller = { caller with
    f_blocks = new_blocks;
    f_max_vreg = !next_vreg - 1;
    f_max_label = max cont_lbl (off_l + callee.f_max_label) } in
  List.map (fun (n, f) -> if n = caller_name then (n, new_caller) else (n, f)) funcs

(* ---- 在主 pass 中反复扫描 call site 并内联 ----------------------------- *)

(* 在函数 f 中寻找对 target 的第一个 call site *)
let find_call_site (f : func) (target : string) : (label * int * value list) option =
  let rec find_in_blocks = function
    | [] -> None
    | (lbl, bb) :: rest ->
        let rec find_in_instrs idx = function
          | [] -> find_in_blocks rest
          | Call { fn; args; _ } :: _ when fn = target -> Some (lbl, idx, args)
          | _ :: tl -> find_in_instrs (idx + 1) tl
        in
        find_in_instrs 0 bb.bb_instrs
  in
  find_in_blocks f.f_blocks

let run (m : module_) : module_ =
  (* 候选函数先只做结构过滤；真正是否内联，延迟到具体调用点再判定。 *)
  let candidates = List.filter (fun (_, f) ->
    f.f_name <> "main" && not (is_recursive f) && is_leaf f
  ) m.m_funcs in

  let rec inline_functions funcs = function
    | [] -> funcs
    | (callee_name, callee) :: rest ->
      let rec inline_calls funcs =
        (* 在任意非 callee 函数中寻找对 callee 的调用 *)
        match List.find_map (fun (n, f) ->
          if n = callee_name then None
          else match find_call_site f callee_name with
            | None -> None
            | Some (lbl, idx, args) ->
                if should_inline_call { m with m_funcs = funcs } callee args
                then Some (n, lbl, idx)
                else None
        ) funcs with
        | None -> funcs
        | Some (caller_name, lbl, idx) ->
            let funcs = inline_one_call funcs caller_name lbl idx callee_name in
            inline_calls funcs
      in
      let funcs = inline_calls funcs in
      (* 删除 callee (如果不再被调用) *)
      let remaining_calls = count_call_sites { m with m_funcs = funcs } callee_name in
      let funcs = if remaining_calls = 0 then
        List.filter (fun (n, _) -> n <> callee_name) funcs
      else funcs in
      inline_functions funcs rest
  in

  let funcs = inline_functions m.m_funcs candidates in
  { m with m_funcs = funcs }
