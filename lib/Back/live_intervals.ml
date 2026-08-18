(* ToyC 活跃区间分析 — 基于 def-use + 线性化
   为每个 vreg 计算 [start, stop] 区间，供线性扫描寄存器分配使用 *)

open Ir_types

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

type interval = {
  vreg  : int;
  start : int;   (* 定义位置 *)
  stop  : int;   (* 最后使用位置 *)
}

(* 线性化: 给每个指令编号 *)

(* 基本块的位置信息 *)
type block_range = {
  block_start : int;  (* phi 定义在此, 第一个 phi 的位置 *)
  block_end   : int;  (* terminator 位置 *)
}

(* 指令位置: (label, instr_index) → 全局位置, terminator 的 instr_index = -1 *)
module LabelIdx = struct
  type t = label * int
  let compare (l1, i1) (l2, i2) =
    let c = compare l1 l2 in if c <> 0 then c else compare i1 i2
end
module PosMap = Map.Make (LabelIdx)

type func_linear = {
  block_ranges : block_range IntMap.t;     (* label → 块范围 *)
  instr_pos    : int PosMap.t;             (* (label, idx) → 全局位置 *)
}

let linearize (f : func) : func_linear =
  let block_ranges = ref IntMap.empty in
  let instr_pos = ref PosMap.empty in
  let next = ref 0 in
  List.iter (fun (lbl, bb) ->
    let n_instrs = List.length bb.bb_instrs in
    let start = !next in
    (* phi 定义: 每个 phi 占一个位置 *)
    List.iteri (fun i _ -> instr_pos := PosMap.add (lbl, i) !next !instr_pos) bb.bb_instrs;
    next := !next + n_instrs;
    (* terminator *)
    let term_pos = !next in
    next := !next + 1;
    instr_pos := PosMap.add (lbl, -1) term_pos !instr_pos;
    block_ranges := IntMap.add lbl { block_start = start; block_end = term_pos } !block_ranges
  ) f.f_blocks;
  { block_ranges = !block_ranges; instr_pos = !instr_pos }

(* phi 从 pred 来的源使用: 发生在 pred 的 terminator 位置 *)
let phi_source_pos (lin : func_linear) (pred_lbl : label) : int =
  try (IntMap.find pred_lbl lin.block_ranges).block_end
  with Not_found -> failwith (Printf.sprintf "phi: predecessor bb%d not found" pred_lbl)

(* 查到给定 (label, idx) 的全局位置 *)
let global_pos (lin : func_linear) (lbl : label) (idx : int) : int =
  try PosMap.find (lbl, idx) lin.instr_pos
  with Not_found -> failwith (Printf.sprintf "pos: bb%d[%d] not found" lbl idx)

let block_map (f : func) : basic_block IntMap.t =
  List.fold_left (fun acc (lbl, bb) -> IntMap.add lbl bb acc) IntMap.empty f.f_blocks

let is_phi_site (blocks : basic_block IntMap.t) (lbl : label) (idx : int) : bool =
  if idx < 0 then false
  else
    match IntMap.find_opt lbl blocks with
    | None -> false
    | Some bb ->
        begin
          match List.nth_opt bb.bb_instrs idx with
          | Some (Phi _) -> true
          | _ -> false
        end

(* 区间计算 *)

let compute (f : func) : interval list =
  let lin = linearize f in
  let blocks = block_map f in
  let du = Ir_analysis.build_def_use { m_globals = []; m_funcs = [ (f.f_name, f) ] } in
  let live = Live_var.analyze f in

  let all_vregs = ref IntSet.empty in
  Ir_analysis.VMap.iter (fun vreg _ -> all_vregs := IntSet.add vreg !all_vregs) du.def_site;
  Ir_analysis.VMap.iter (fun vreg _ -> all_vregs := IntSet.add vreg !all_vregs) du.use_sites;
  (* 添加形参 vreg *)
  List.iter (fun (_, vreg) -> all_vregs := IntSet.add vreg !all_vregs) f.f_params;

  (* 跳过 VReg(-1) — mem2reg 的 undef 哨兵，无定义点，无需分配活跃区间 *)
  IntSet.fold (fun vreg acc ->
    if vreg < 0 then acc
    else
    let def_pos =
      match Ir_analysis.VMap.find_opt vreg du.def_site with
      | Some (def_lbl, def_idx) -> global_pos lin def_lbl def_idx
      | None -> -1  (* 形参或隐式定义: 在函数入口前定义 *)
    in

    let use_positions = ref [ def_pos ] in
    begin match Ir_analysis.VMap.find_opt vreg du.use_sites with
    | Some sites ->
      List.iter (fun (lbl, idx) ->
          if not (is_phi_site blocks lbl idx) then
            use_positions := global_pos lin lbl idx :: !use_positions
      ) sites
    | None -> ()
    end;
      (* 只看“定义点到最后一次文本 use”会漏掉 CFG 上的 live-through。
         例如值在 block A 中定义，在后继 block B 中继续活跃，但最后一次显式 use
         出现在按线性顺序更早的另一个块里；若不把 live_in/live_out 折进区间，
         线性扫描会错误复用寄存器。这里对齐 LLVM LiveIntervals 的思路，
         将所有 live-through block 的首尾 slot 也并入区间。 *)
      IntMap.iter (fun lbl range ->
        let live_in =
          match IntMap.find_opt lbl live.Live_var.live_in with
          | Some set -> IntSet.mem vreg set
          | None -> false
        in
        let live_out =
          match IntMap.find_opt lbl live.Live_var.live_out with
          | Some set -> IntSet.mem vreg set
          | None -> false
        in
        if live_in then
          use_positions := range.block_start :: !use_positions;
        if live_out then
          use_positions := range.block_end :: !use_positions
      ) lin.block_ranges;
    List.iter (fun (_, bb) ->
      List.iter (fun instr ->
        match instr with
        | Phi { incoming; _ } ->
          List.iter (fun (v, pred) ->
            if v = VReg vreg then
              use_positions := phi_source_pos lin pred :: !use_positions
          ) incoming
        | _ -> ()
      ) bb.bb_instrs
    ) f.f_blocks;
    let stop = List.fold_left max def_pos !use_positions in
    { vreg; start = def_pos; stop } :: acc
  ) !all_vregs []

let compute_module (m : module_) : (string * interval list) list =
  List.map (fun (name, f) -> (name, compute f)) m.m_funcs
