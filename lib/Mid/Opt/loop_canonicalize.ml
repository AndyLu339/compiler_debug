(* ToyC 优化 — 循环规范化

   先把可处理的自然循环
   规整到更适合后续 loop passes 消费的形态上。

   当前实现先补两层基础规范化：
   1. preheader insertion
      把所有来自 loop 外的 header 入边统一收进一个 preheader 块；
   2. dedicated exit insertion
      把 loop 内到 exit block 的边统一先落到专属 exit 块。

   完成这两步后，再用 rotate 变换，把简单 while
   进一步整理成更接近 bottom-test 的形状。 *)

open Ir_types
open Loop_info

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

let build_bmap (f : func) : basic_block IntMap.t =
  List.fold_left (fun m (lbl, bb) -> IntMap.add lbl bb m) IntMap.empty f.f_blocks

let term_succs = function
  | Jump l -> [ l ]
  | Br (_, t, f) -> [ t; f ]
  | Ret _ -> []

let build_succs (bmap : basic_block IntMap.t) : IntSet.t IntMap.t =
  IntMap.fold (fun lbl bb m ->
    IntMap.add lbl (IntSet.of_list (term_succs bb.bb_term)) m
  ) bmap IntMap.empty

let build_preds (bmap : basic_block IntMap.t) : IntSet.t IntMap.t =
  predecessors (build_succs bmap)

let partition_phis (bb : basic_block) : instr list * instr list =
  let rec take acc = function
    | Phi _ as i :: tl -> take (i :: acc) tl
    | rest -> (List.rev acc, rest)
  in
  take [] bb.bb_instrs

let rewrite_succ old_lbl new_lbl = function
  | Jump lbl when lbl = old_lbl -> Jump new_lbl
  | Br (cond, t, f) ->
      let t = if t = old_lbl then new_lbl else t in
      let f = if f = old_lbl then new_lbl else f in
      Br (cond, t, f)
  | term -> term

let outside_preds (preds : IntSet.t IntMap.t) (lp : loop) : label list =
  match IntMap.find_opt lp.header preds with
  | None -> []
  | Some ps ->
      IntSet.elements (IntSet.filter (fun p -> not (IntSet.mem p lp.blocks)) ps)

let fresh_vreg next =
  let v = !next in
  incr next;
  v

let fresh_label next =
  let l = !next in
  incr next;
  l

let insert_preheader_for_loop (f : func) (lp : loop)
    : (basic_block IntMap.t * int * int) option =
  let bmap = build_bmap f in
  let preds = build_preds bmap in
  let outs = outside_preds preds lp in
  match outs with
  | [] -> None
  | [ pred ] ->
      let pred_bb = IntMap.find pred bmap in
      if pred_bb.bb_term = Jump lp.header then None
      else
        let next_label = ref (f.f_max_label + 1) in
        let next_vreg = ref (f.f_max_vreg + 1) in
        let new_pre = fresh_label next_label in
        let header_bb = IntMap.find lp.header bmap in
        let phis, rest = partition_phis header_bb in
        let new_pre_phis, new_header_phis =
          List.fold_right (fun instr (acc_pre, acc_hdr) ->
            match instr with
            | Phi { dst; incoming } ->
                let outside_in = List.filter (fun (_, lbl) -> lbl = pred) incoming in
                if outside_in = [] then
                  (acc_pre, instr :: acc_hdr)
                else
                  let inside_in = List.filter (fun (_, lbl) -> lbl <> pred) incoming in
                  let pre_dst = fresh_vreg next_vreg in
                  let pre_phi = Phi { dst = pre_dst; incoming = outside_in } in
                  let hdr_phi =
                    Phi { dst; incoming = inside_in @ [ (VReg pre_dst, new_pre) ] }
                  in
                  (pre_phi :: acc_pre, hdr_phi :: acc_hdr)
            | _ -> (acc_pre, instr :: acc_hdr)
          ) phis ([], [])
        in
        let header_bb = { header_bb with bb_instrs = new_header_phis @ rest } in
        let pre_bb = { bb_label = new_pre; bb_instrs = new_pre_phis; bb_term = Jump lp.header } in
        let bmap =
          IntMap.map (fun bb ->
            if bb.bb_label = pred then { bb with bb_term = rewrite_succ lp.header new_pre bb.bb_term }
            else bb
          ) bmap
        in
        let bmap = IntMap.add lp.header header_bb bmap in
        let bmap = IntMap.add new_pre pre_bb bmap in
        Some (bmap, !next_label - 1, !next_vreg - 1)
  | _ ->
      let next_label = ref (f.f_max_label + 1) in
      let next_vreg = ref (f.f_max_vreg + 1) in
      let new_pre = fresh_label next_label in
      let header_bb = IntMap.find lp.header bmap in
      let phis, rest = partition_phis header_bb in
      let outside_set = IntSet.of_list outs in
      let new_pre_phis, new_header_phis =
        List.fold_right (fun instr (acc_pre, acc_hdr) ->
          match instr with
          | Phi { dst; incoming } ->
              let outside_in =
                List.filter (fun (_, lbl) -> IntSet.mem lbl outside_set) incoming
              in
              if outside_in = [] then
                (acc_pre, instr :: acc_hdr)
              else
                let inside_in =
                  List.filter (fun (_, lbl) -> not (IntSet.mem lbl outside_set)) incoming
                in
                let pre_dst = fresh_vreg next_vreg in
                let pre_phi = Phi { dst = pre_dst; incoming = outside_in } in
                let hdr_phi =
                  Phi { dst; incoming = inside_in @ [ (VReg pre_dst, new_pre) ] }
                in
                (pre_phi :: acc_pre, hdr_phi :: acc_hdr)
          | _ -> (acc_pre, instr :: acc_hdr)
        ) phis ([], [])
      in
      let header_bb = { header_bb with bb_instrs = new_header_phis @ rest } in
      let pre_bb = { bb_label = new_pre; bb_instrs = new_pre_phis; bb_term = Jump lp.header } in
      let outside_set = IntSet.of_list outs in
      let bmap =
        IntMap.map (fun bb ->
          if IntSet.mem bb.bb_label outside_set then
            { bb with bb_term = rewrite_succ lp.header new_pre bb.bb_term }
          else bb
        ) bmap
      in
      let bmap = IntMap.add lp.header header_bb bmap in
      let bmap = IntMap.add new_pre pre_bb bmap in
      Some (bmap, !next_label - 1, !next_vreg - 1)

let split_dedicated_exit_for_loop (f : func) (lp : loop)
    : (basic_block IntMap.t * int * int) option =
  let bmap = build_bmap f in
  let preds = build_preds bmap in
  let exits = lp.exits |> List.sort_uniq compare in
  let rec find_target = function
    | [] -> None
    | exit_lbl :: tl ->
        let pred_set = match IntMap.find_opt exit_lbl preds with Some s -> s | None -> IntSet.empty in
        let inside_preds = IntSet.filter (fun p -> IntSet.mem p lp.blocks) pred_set in
        let outside_preds = IntSet.filter (fun p -> not (IntSet.mem p lp.blocks)) pred_set in
        if IntSet.is_empty inside_preds || IntSet.is_empty outside_preds then
          find_target tl
        else
          Some (exit_lbl, inside_preds)
  in
  match find_target exits with
  | None -> None
  | Some (exit_lbl, inside_preds) ->
      let next_label = ref (f.f_max_label + 1) in
      let next_vreg = ref (f.f_max_vreg + 1) in
      let new_exit = fresh_label next_label in
      let exit_bb = IntMap.find exit_lbl bmap in
      let phis, rest = partition_phis exit_bb in
      let new_exit_phis, new_exit_bb_phis =
        List.fold_right (fun instr (acc_mid, acc_exit) ->
          match instr with
          | Phi { dst; incoming } ->
              let from_loop =
                List.filter (fun (_, pred) -> IntSet.mem pred inside_preds) incoming
              in
              if from_loop = [] then
                (acc_mid, instr :: acc_exit)
              else
                let from_outside =
                  List.filter (fun (_, pred) -> not (IntSet.mem pred inside_preds)) incoming
                in
                let mid_dst = fresh_vreg next_vreg in
                let mid_phi = Phi { dst = mid_dst; incoming = from_loop } in
                let exit_phi =
                  Phi { dst; incoming = from_outside @ [ (VReg mid_dst, new_exit) ] }
                in
                (mid_phi :: acc_mid, exit_phi :: acc_exit)
          | _ -> (acc_mid, instr :: acc_exit)
        ) phis ([], [])
      in
      let exit_bb = { exit_bb with bb_instrs = new_exit_bb_phis @ rest } in
      let middle_bb = { bb_label = new_exit; bb_instrs = new_exit_phis; bb_term = Jump exit_lbl } in
      let bmap =
        IntMap.map (fun bb ->
          if IntSet.mem bb.bb_label inside_preds then
            { bb with bb_term = rewrite_succ exit_lbl new_exit bb.bb_term }
          else bb
        ) bmap
      in
      let bmap = IntMap.add exit_lbl exit_bb bmap in
      let bmap = IntMap.add new_exit middle_bb bmap in
      Some (bmap, !next_label - 1, !next_vreg - 1)

let canonicalize_func (f : func) : func =
  let rec fixpoint (f : func) =
    let dom = Dominance.analyze f in
    let li = analyze f dom in
    let loops =
      List.sort (fun a b ->
        let c = compare b.depth a.depth in
        if c <> 0 then c else compare a.header b.header
      ) li.loops
    in
    let try_preheaders =
      List.find_map (insert_preheader_for_loop f) loops
    in
    match try_preheaders with
    | Some (bmap, max_label, max_vreg) ->
        fixpoint
          { f with
            f_blocks = IntMap.bindings bmap |> List.sort (fun (a, _) (b, _) -> compare a b);
            f_max_label = max_label;
            f_max_vreg = max_vreg }
    | None ->
        let try_exits =
          List.find_map (split_dedicated_exit_for_loop f) loops
        in
        match try_exits with
        | Some (bmap, max_label, max_vreg) ->
            fixpoint
              { f with
                f_blocks = IntMap.bindings bmap |> List.sort (fun (a, _) (b, _) -> compare a b);
                f_max_label = max_label;
                f_max_vreg = max_vreg }
        | None -> f
  in
  fixpoint f

let run (m : module_) : module_ =
  let m =
    { m with
      m_funcs = List.map (fun (n, f) -> (n, canonicalize_func f)) m.m_funcs }
  in
  Loop_rotate.run m
