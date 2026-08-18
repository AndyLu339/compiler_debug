(* ToyC 优化 — SimplifyCFG (控制流化简)
   在 SSA 上做三件局部重写, 迭代至不动点:
   1. 分支化简: Br(cond, L, L) → Jump L
   2. phi 简化: 去重 incoming 标签; 全部 incoming 值相同 → Copy dst v
   3. 块合并: 单前驱单后继的直通块 B 并入前驱 A
      (B 的 phi → Copy, 全局把 phi incoming 里的 label B 重写为 A) *)

open Ir_types

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

(* ---- 前驱计算 -------------------------------------------------------- *)

let compute_preds (bmap : basic_block IntMap.t) : IntSet.t IntMap.t =
  let preds = ref IntMap.empty in
  IntMap.iter (fun lbl bb ->
    let succs = match bb.bb_term with
      | Jump l -> [ l ]
      | Br (_, t, f) -> [ t; f ]
      | Ret _ -> []
    in
    List.iter (fun s ->
      if IntMap.mem s bmap then
        preds := IntMap.update s (fun prev ->
          Some (IntSet.add lbl (Option.value ~default:IntSet.empty prev))
        ) !preds
    ) succs
  ) bmap;
  !preds

(* ---- phi 简化 -------------------------------------------------------- *)

(* 按 label 去重, 保留首个出现的 (value, label) *)
let dedup_incoming (incoming : (value * label) list) : (value * label) list =
  let seen = ref IntSet.empty in
  List.filter (fun (_, lbl) ->
    if IntSet.mem lbl !seen then false
    else (seen := IntSet.add lbl !seen; true)
  ) incoming

(* 全部 incoming 值相同 → Copy; 否则去重后原样保留 *)
let simplify_phi_instr (instr : instr) : instr =
  match instr with
  | Phi { dst; incoming } ->
      let incoming = dedup_incoming incoming in
      (match incoming with
       | [] -> instr
       | (v0, _) :: rest ->
           if List.for_all (fun (v, _) -> v = v0) rest then
             Copy { dst; src = v0 }
           else
             Phi { dst; incoming })
  | _ -> instr

(* ---- 块合并 ---------------------------------------------------------- *)

(* b 的终结指令是否回指 a (即存在 b→a 的边)。
   若存在, 合并会让 a 的 phi 产生自环 incoming, 必须跳过。 *)
let targets_a (b_bb : basic_block) (a : label) : bool =
  match b_bb.bb_term with
  | Jump t -> t = a
  | Br (_, t, f) -> t = a || f = a
  | Ret _ -> false

(* 找一个可合并的块 b: b 唯一前驱 a, a 的终结是 Jump b (唯一后继),
   且 b 不回指 a。返回 (a, b)。 *)
let find_mergeable (bmap : basic_block IntMap.t) (preds : IntSet.t IntMap.t)
    : (label * label) option =
  let exception Found of (label * label) in
  try
    IntMap.iter (fun b b_bb ->
      let ps = match IntMap.find_opt b preds with
        | Some p -> p | None -> IntSet.empty
      in
      if IntSet.cardinal ps = 1 then begin
        let a = IntSet.choose ps in
        if a <> b then
          match IntMap.find_opt a bmap with
          | Some a_bb ->
              (match a_bb.bb_term with
               | Jump t when t = b && not (targets_a b_bb a) ->
                   raise (Found (a, b))
               | _ -> ())
          | None -> ()
      end
    ) bmap;
    None
  with Found pair -> Some pair

(* 将 b 并入 a: b 的 phi 转 Copy, 指令拼到 a 后, a 的终结改为 b 的终结,
   删除 b, 并把所有 phi incoming 里的 label b 重写为 a。 *)
let merge_into (bmap : basic_block IntMap.t) (a : label) (b : label)
    : basic_block IntMap.t =
  let a_bb = IntMap.find a bmap in
  let b_bb = IntMap.find b bmap in
  let b_phis, b_rest =
    List.partition (function Phi _ -> true | _ -> false) b_bb.bb_instrs
  in
  let copies =
    List.map (function
      | Phi { dst; incoming } ->
          let v = match incoming with (v, _) :: _ -> v | [] -> Imm 0 in
          Copy { dst; src = v }
      | _ -> assert false) b_phis
  in
  let merged_bb =
    { bb_label = a;
      bb_instrs = a_bb.bb_instrs @ copies @ b_rest;
      bb_term = b_bb.bb_term }
  in
  let bmap = IntMap.add a merged_bb (IntMap.remove b bmap) in
  IntMap.map (fun bb ->
    { bb with bb_instrs = List.map (function
        | Phi { dst; incoming } ->
            Phi { dst; incoming = List.map (fun (v, lbl) ->
                (v, if lbl = b then a else lbl)) incoming }
        | i -> i
      ) bb.bb_instrs }
  ) bmap

(* ---- 单函数 ---------------------------------------------------------- *)

let run_on_func (f : func) : func =
  let block_map =
    List.fold_left (fun m (l, bb) -> IntMap.add l bb m) IntMap.empty f.f_blocks
  in

  let rec merge_all bmap =
    let preds = compute_preds bmap in
    match find_mergeable bmap preds with
    | Some (a, b) -> merge_all (merge_into bmap a b)
    | None -> bmap
  in

  let rec fixpoint bmap =
    let changed = ref false in

    (* Step 1: Br(cond, L, L) → Jump L *)
    let bmap = IntMap.map (fun bb ->
      match bb.bb_term with
      | Br (_, t, f) when t = f ->
          changed := true;
          { bb with bb_term = Jump t }
      | _ -> bb
    ) bmap in

    (* Step 2: phi 简化 *)
    let bmap = IntMap.map (fun bb ->
      let new_instrs = List.map simplify_phi_instr bb.bb_instrs in
      if new_instrs <> bb.bb_instrs then changed := true;
      { bb with bb_instrs = new_instrs }
    ) bmap in

    (* Step 3: 块合并 (合并所有可合并的, 直到没有) *)
    let before_count = IntMap.cardinal bmap in
    let bmap = merge_all bmap in
    if IntMap.cardinal bmap <> before_count then changed := true;

    if !changed then fixpoint bmap else bmap
  in

  let new_bmap = fixpoint block_map in
  { f with f_blocks = IntMap.bindings new_bmap
                     |> List.sort (fun (a, _) (b, _) -> compare a b) }

(* ---- 入口 ------------------------------------------------------------ *)

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
