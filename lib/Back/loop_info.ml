(* ToyC 循环识别 — 自然循环检测 
   算法: 支配树 + 回边 → 反向遍历构造循环体 *)

open Ir_types

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

type loop = {
  header   : label;           (* 循环入口, 支配循环内所有节点 *)
  preheader: label option;    (* 前置块, 不在循环内, 唯一入口到 header *)
  latches  : label list;      (* 锁存器: 循环内有回边到 header 的块 *)
  blocks   : IntSet.t;        (* 循环体内所有节点, 含 header *)
  exiting  : label list;      (* 退出块: 循环内有边离开循环的块 *)
  exits    : label list;      (* 出口块: 离开循环后到达的块 *)
  parent   : label option;    (* 外部循环的 header, None 表示顶层 *)
  depth    : int;             (* 嵌套深度, 顶层=1 *)
}

type loop_info = {
  loops      : loop list;      (* 所有循环的列表 *)
  loop_of    : IntSet.t IntMap.t;  (* 块 → 所在最内层循环的 header *)
  loop_depth : int IntMap.t;       (* 块 → 嵌套深度, 0 = 不在循环内 *)
}

(* 从后继计算前驱 *)
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

(* 找回边: n → d 且 d 支配 n *)
let find_back_edges (f : func) (dom : Dominance.dom_info) : (label * label) list =
  let succs = ref IntMap.empty in
  List.iter (fun (lbl, bb) ->
    let targets = match bb.bb_term with
      | Jump l -> [l] | Br (_, t, f) -> [t; f] | Ret _ -> []
    in
    succs := IntMap.add lbl (IntSet.of_list targets) !succs
  ) f.f_blocks;
  let back_edges = ref [] in
  IntMap.iter (fun n targets ->
    IntSet.iter (fun d ->
      if IntSet.mem d (IntMap.find n dom.doms) then
        back_edges := (n, d) :: !back_edges
    ) targets
  ) !succs;
  !back_edges

(* 对一条回边 n→d 构造循环体: 从 n 反向遍历, 遇 d 停止 *)
let build_loop_body (n : label) (d : label) (preds : IntSet.t IntMap.t) : IntSet.t =
  let visited = ref (IntSet.singleton d) in
  let stack = ref [ n ] in
  while !stack <> [] do
    let m = List.hd !stack in
    stack := List.tl !stack;
    if not (IntSet.mem m !visited) then begin
      visited := IntSet.add m !visited;
      let pred_set = try IntMap.find m preds with Not_found -> IntSet.empty in
      IntSet.iter (fun p -> stack := p :: !stack) pred_set
    end
  done;
  !visited

(* 构建单个循环的信息 *)
let build_loop (header : label) (body_blocks : IntSet.t) (latches : label list)
    (succs : IntSet.t IntMap.t) (preds : IntSet.t IntMap.t) (depth : int)
    (parent : label option) : loop =
  let exiting = ref [] in
  let exits = ref [] in
  IntSet.iter (fun blk ->
    let succ_set = try IntMap.find blk succs with Not_found -> IntSet.empty in
    IntSet.iter (fun s ->
      if not (IntSet.mem s body_blocks) then begin
        exiting := blk :: !exiting;
        exits := s :: !exits
      end
    ) succ_set
  ) body_blocks;

  let preheader =
    let pred_set = try IntMap.find header preds with Not_found -> IntSet.empty in
    let non_loop_preds = IntSet.filter (fun p -> not (IntSet.mem p body_blocks)) pred_set in
    if IntSet.cardinal non_loop_preds = 1 then Some (IntSet.choose non_loop_preds) else None
  in

  { header; preheader; latches;
    blocks = body_blocks; exiting = !exiting; exits = !exits;
    parent; depth }

(* 合并共享 header 的循环 *)
let merge_loops (loops : loop list) : loop list =
  let by_header = ref IntMap.empty in
  List.iter (fun lp ->
    by_header := IntMap.update lp.header (fun prev ->
      Some (lp :: (match prev with None -> [] | Some lst -> lst))
    ) !by_header
  ) loops;
  IntMap.fold (fun header lp_list acc ->
    if List.length lp_list = 1 then
      (List.hd lp_list) :: acc
    else
      let merged_blocks = List.fold_left (fun s lp ->
        IntSet.union s lp.blocks
      ) IntSet.empty lp_list in
      let merged_latches = List.concat_map (fun lp -> lp.latches) lp_list in
      { header;
        preheader = (List.hd lp_list).preheader;
        latches = merged_latches;
        blocks = merged_blocks;
        exiting = (List.hd lp_list).exiting;
        exits = (List.hd lp_list).exits;
        parent = (List.hd lp_list).parent;
        depth = (List.hd lp_list).depth
      } :: acc
  ) !by_header []

(* 计算嵌套关系和深度 *)
let compute_nesting (loops : loop list) : loop list =
  let header_to_loop = List.fold_left (fun m lp ->
    IntMap.add lp.header lp m
  ) IntMap.empty loops in
  List.map (fun lp ->
    let dom = ref None in
    let min_depth_above = ref max_int in
    IntMap.iter (fun h other ->
      if h <> lp.header then
        if IntSet.subset lp.blocks other.blocks
           && IntSet.cardinal other.blocks > IntSet.cardinal lp.blocks
           && other.depth < !min_depth_above then begin
          dom := Some h;
          min_depth_above := other.depth
        end
    ) header_to_loop;
    let depth = match !dom with Some _ -> !min_depth_above + 1 | None -> 1 in
    { lp with parent = !dom; depth }
  ) loops

(* 入口 *)
let analyze (f : func) (dom : Dominance.dom_info) : loop_info =
  let succs = ref IntMap.empty in
  List.iter (fun (lbl, bb) ->
    let targets = match bb.bb_term with
      | Jump l -> [l] | Br (_, t, f) -> [t; f] | Ret _ -> []
    in
    succs := IntMap.add lbl (IntSet.of_list targets) !succs
  ) f.f_blocks;
  let preds = predecessors !succs in

  let back_edges = find_back_edges f dom in

  let raw_loops =
    List.map (fun (n, d) ->
      let body = build_loop_body n d preds in
      let latches = List.filter (fun (_, d') -> d' = d) back_edges
                     |> List.map fst in
      build_loop d body latches !succs preds 1 None
    ) back_edges
  in

  let merged = merge_loops raw_loops in
  let nested = compute_nesting merged in

  let loop_of = ref IntMap.empty in
  List.iter (fun lp ->
    IntSet.iter (fun blk ->
      match IntMap.find_opt blk !loop_of with
      | None -> loop_of := IntMap.add blk (IntSet.singleton lp.header) !loop_of
      | Some existing ->
        let header_loop = List.find (fun l -> l.header = lp.header) nested in
        let existing_loop = List.find (fun l -> l.header = IntSet.choose existing) nested in
        if header_loop.depth > existing_loop.depth then
          loop_of := IntMap.add blk (IntSet.singleton lp.header) !loop_of
    ) lp.blocks
  ) nested;

  let loop_depth = ref IntMap.empty in
  List.iter (fun lp ->
    IntSet.iter (fun blk ->
      match IntMap.find_opt blk !loop_depth with
      | None -> loop_depth := IntMap.add blk lp.depth !loop_depth
      | Some d -> if lp.depth > d then loop_depth := IntMap.add blk lp.depth !loop_depth
    ) lp.blocks
  ) nested;

  { loops = nested;
    loop_of = !loop_of;
    loop_depth = !loop_depth }
