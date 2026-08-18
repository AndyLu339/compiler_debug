(* ToyC 支配树 — 迭代求解 dominator sets + immediate dominators
   算法: Cooper-Harvey-Kennedy, 供 mem2reg / loop_info 使用 *)

open Ir_types

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

type dom_info = {
  idom       : int IntMap.t;      (* 立即支配者, entry idom = entry 自身 *)
  children   : IntSet.t IntMap.t; (* idom → 子节点集合 (支配树) *)
  doms       : IntSet.t IntMap.t; (* 支配集合 *)
  dom_front  : IntSet.t IntMap.t; (* 支配边界 *)
}

(* 计算后继 *)
let successors (f : func) : IntSet.t IntMap.t =
  List.fold_left (fun acc (lbl, bb) ->
    let succs = match bb.bb_term with
      | Jump l       -> [ l ]
      | Br (_, t, f) -> [ t; f ]
      | Ret _        -> []
    in
    IntMap.add lbl (IntSet.of_list succs) acc
  ) IntMap.empty f.f_blocks

(* 从后继反推前驱 *)
let predecessors (succs : IntSet.t IntMap.t) : IntSet.t IntMap.t =
  let preds = ref IntMap.empty in
  IntMap.iter (fun lbl targets ->
    IntSet.iter (fun t ->
      preds := IntMap.update t (fun prev ->
        Some (IntSet.add lbl (match prev with None -> IntSet.empty | Some s -> s))
      ) !preds
    ) targets
  ) succs;
  !preds

(* 迭代求解 dominator sets *)
let compute_doms (labels : label list) (preds : IntSet.t IntMap.t) (entry : label)
    : IntSet.t IntMap.t =
  let all_nodes = IntSet.of_list labels in
  let doms = ref IntMap.empty in
  List.iter (fun lbl ->
    if lbl = entry then
      doms := IntMap.add lbl (IntSet.singleton entry) !doms
    else
      doms := IntMap.add lbl all_nodes !doms
  ) labels;
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun lbl ->
      if lbl <> entry then
        let pred_set = try IntMap.find lbl preds with Not_found -> IntSet.empty in
        let inter =
          IntSet.fold (fun pred acc ->
            match acc with
            | None -> Some (IntMap.find pred !doms)
            | Some s -> Some (IntSet.inter s (IntMap.find pred !doms))
          ) pred_set None
        in
        let new_doms =
          match inter with
          | None -> IntSet.singleton lbl
          | Some s -> IntSet.add lbl s
        in
        let old_doms = IntMap.find lbl !doms in
        if not (IntSet.equal new_doms old_doms) then begin
          doms := IntMap.add lbl new_doms !doms;
          changed := true
        end
    ) labels
  done;
  !doms

(* 从 dom sets 计算 idom:
   idom(n) 是 n 的严格支配者中“最近”的那个。
   参照 LLVM 的语义，立即支配者应被其它所有严格支配者支配；
   不能选离入口最近的那个。 *)
let compute_idoms (labels : label list) (doms : IntSet.t IntMap.t) (entry : label)
    : int IntMap.t =
  let idom = ref IntMap.empty in
  List.iter (fun lbl ->
    if lbl = entry then
      idom := IntMap.add entry entry !idom
    else
      let strict_doms = IntSet.remove lbl (IntMap.find lbl doms) in
      let best =
        IntSet.fold (fun d acc ->
          let is_closer_than_cur cur =
            let cur_doms = IntMap.find cur doms in
            IntSet.mem cur (IntMap.find d doms) && not (IntSet.mem d cur_doms)
          in
          match acc with
          | None -> Some d
          | Some cur -> if is_closer_than_cur cur then Some d else Some cur
        ) strict_doms None
      in
      idom := IntMap.add lbl (match best with Some d -> d | None -> entry) !idom
  ) labels;
  !idom

(* 从 idom 构建 children 映射 *)
let compute_children (labels : label list) (idom : int IntMap.t) : IntSet.t IntMap.t =
  let children = ref IntMap.empty in
  List.iter (fun lbl ->
    let parent = IntMap.find lbl idom in
    if parent <> lbl then
      children := IntMap.update parent (fun prev ->
        Some (IntSet.add lbl (match prev with None -> IntSet.empty | Some s -> s))
      ) !children
  ) labels;
  !children

(* 计算支配边界: DF(d) = { n | d 支配 n 的一个前驱, 但 d 不严格支配 n } *)
let compute_dom_frontier (labels : label list) (doms : IntSet.t IntMap.t)
    (preds : IntSet.t IntMap.t) : IntSet.t IntMap.t =
  let df = ref IntMap.empty in
  List.iter (fun lbl -> df := IntMap.add lbl IntSet.empty !df) labels;
  List.iter (fun n ->
    let pred_set = try IntMap.find n preds with Not_found -> IntSet.empty in
    IntSet.iter (fun p ->
      (* d ∈ doms[p] 保证 d 支配 p, 无需额外检查 *)
      IntSet.iter (fun d ->
        (* d 不严格支配 n ⇔ ¬(d ≠ n ∧ d ∈ doms[n]) *)
        if not (d <> n && IntSet.mem d (IntMap.find n doms)) then
          df := IntMap.update d (fun prev ->
            Some (IntSet.add n (match prev with None -> IntSet.empty | Some s -> s))
          ) !df
      ) (IntMap.find p doms)
    ) pred_set
  ) labels;
  !df

(* 入口 *)
let analyze (f : func) : dom_info =
  let labels = List.map fst f.f_blocks in
  let succs = successors f in
  let preds = predecessors succs in
  let entry = f.f_entry in
  let doms = compute_doms labels preds entry in
  let idom = compute_idoms labels doms entry in
  let children = compute_children labels idom in
  let dom_front = compute_dom_frontier labels doms preds in
  { idom; children; doms; dom_front }
