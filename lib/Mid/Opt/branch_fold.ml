(* ToyC 优化 — 无用分支消除
   在 SSA 上做:
   1. Br Imm 0/1 → Jump (常量条件来自 const_fold + copy_prop + const_prop)
   2. 删除不可达块
   3. 修复 Phi 的 incoming 列表
   迭代至不动点 *)

open Ir_types

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

let has_phi (bb : basic_block) =
  List.exists (function Phi _ -> true | _ -> false) bb.bb_instrs

let is_empty_jump_block (bb : basic_block) =
  bb.bb_instrs = []
  &&
  match bb.bb_term with
  | Jump succ when succ <> bb.bb_label -> true
  | _ -> false

(* ---- 可达性分析 ------------------------------------------------------ *)

let compute_reachable (bmap : basic_block IntMap.t) (entry : label) : IntSet.t =
  let reachable = ref IntSet.empty in
  let rec dfs lbl =
    if not (IntSet.mem lbl !reachable) && IntMap.mem lbl bmap then begin
      reachable := IntSet.add lbl !reachable;
      let bb = IntMap.find lbl bmap in
      match bb.bb_term with
      | Jump l -> dfs l
      | Br (_, t, f) -> dfs t; dfs f
      | Ret _ -> ()
    end
  in
  dfs entry;
  !reachable

(* ---- 前驱计算 -------------------------------------------------------- *)

let compute_preds (bmap : basic_block IntMap.t) : IntSet.t IntMap.t =
  let preds = ref IntMap.empty in
  IntMap.iter (fun lbl bb ->
    let succs = match bb.bb_term with
      | Jump l -> [l] | Br (_, t, f) -> [t; f] | Ret _ -> []
    in
    List.iter (fun s ->
      if IntMap.mem s bmap then
        preds := IntMap.update s (fun prev ->
          Some (IntSet.add lbl (Option.value ~default:IntSet.empty prev))
        ) !preds
    ) succs
  ) bmap;
  !preds

(* ---- Phi 修复 -------------------------------------------------------- *)

let fix_phis (bmap : basic_block IntMap.t) (preds : IntSet.t IntMap.t) =
  IntMap.map (fun bb ->
    let my_preds = match IntMap.find_opt bb.bb_label preds with
      | Some p -> p | None -> IntSet.empty in
    let new_instrs = List.filter_map (fun instr ->
      match instr with
      | Phi { dst; incoming } ->
          let new_incoming = List.filter (fun (_, lbl) ->
            IntSet.mem lbl my_preds
          ) incoming in
          (match new_incoming with
           | [] -> None
           | _  -> Some (Phi { dst; incoming = new_incoming }))
      | _ -> Some instr
    ) bb.bb_instrs in
    { bb with bb_instrs = new_instrs }
  ) bmap

(* ---- 空跳转块压平 ---------------------------------------------------- *)

let rewrite_targets_through_empty_jumps (bmap : basic_block IntMap.t) (entry : label) =
  let rec resolve seen lbl =
    if IntSet.mem lbl seen then lbl
    else
      match IntMap.find_opt lbl bmap with
      | Some bb when is_empty_jump_block bb ->
          begin match bb.bb_term with
          | Jump succ ->
              let succ_has_phi =
                match IntMap.find_opt succ bmap with
                | Some succ_bb -> has_phi succ_bb
                | None -> false
              in
              if succ_has_phi then lbl
              else resolve (IntSet.add lbl seen) succ
          | _ ->
              lbl
          end
      | _ ->
          lbl
  in
  let changed = ref false in
  let rewrite_lbl lbl =
    let lbl' = resolve IntSet.empty lbl in
    if lbl' <> lbl then changed := true;
    lbl'
  in
  let rewrite_term = function
    | Jump lbl ->
        Jump (rewrite_lbl lbl)
    | Br (cond, t, f) ->
        Br (cond, rewrite_lbl t, rewrite_lbl f)
    | Ret _ as term ->
        term
  in
  let bmap =
    IntMap.map (fun bb -> { bb with bb_term = rewrite_term bb.bb_term }) bmap
  in
  let entry' = rewrite_lbl entry in
  (bmap, entry', !changed)

(* ---- 单个函数 -------------------------------------------------------- *)

let run_on_func (f : func) : func =
  let block_map = List.fold_left (fun m (l, bb) -> IntMap.add l bb m)
      IntMap.empty f.f_blocks in

  let rec fixpoint (bmap : basic_block IntMap.t) (entry : label)
      : basic_block IntMap.t * label =
    (* Step 1: 折叠 Br Imm → Jump *)
    let folded = ref false in
    let bmap = IntMap.map (fun bb ->
      match bb.bb_term with
      | Br (Imm 0, _, f) -> folded := true; { bb with bb_term = Jump f }
      | Br (Imm _, t, _) -> folded := true; { bb with bb_term = Jump t }
      | _ -> bb
    ) bmap in
    (* Step 2: 压平空跳转块链 *)
    let bmap, entry, threaded = rewrite_targets_through_empty_jumps bmap entry in
    (* Step 3: 删除不可达块 *)
    let reachable = compute_reachable bmap entry in
    let all_labels = IntMap.fold (fun l _ s -> IntSet.add l s) bmap IntSet.empty in
    let removed = IntSet.exists (fun l -> not (IntSet.mem l reachable)) all_labels in
    if not !folded && not threaded && not removed then (bmap, entry)
    else
      let bmap = IntMap.filter (fun l _ -> IntSet.mem l reachable) bmap in
      let preds = compute_preds bmap in
      let bmap = fix_phis bmap preds in
      fixpoint bmap entry
  in

  let new_blocks, new_entry = fixpoint block_map f.f_entry in
  { f with f_blocks = IntMap.bindings new_blocks
                     |> List.sort (fun (a,_) (b,_) -> compare a b);
           f_entry = new_entry }

(* ---- 入口 ------------------------------------------------------------ *)

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
