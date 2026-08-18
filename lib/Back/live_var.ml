(* ToyC 活变量分析 *)

open Ir_types

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

type liveness = {
  live_in  : IntSet.t IntMap.t;   (* label → 基本块入口活跃 vreg 集 *)
  live_out : IntSet.t IntMap.t;   (* label → 基本块出口活跃 vreg 集 *)
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

(* 提取 vreg *)
let vregs_of_values vs =
  (* 跳过 VReg(-1) — mem2reg 的 undef 哨兵，不代表真实寄存器，无需追踪活跃性 *)
  List.filter_map
    (function VReg r when r >= 0 -> Some r | Imm _ | Global _ | VReg _ -> None)
    vs
  |> IntSet.of_list

(* 基本块内定义的 vreg *)
let block_defs (bb : basic_block) : IntSet.t =
  List.filter_map instr_dst bb.bb_instrs
  |> IntSet.of_list

(* 基本块内使用的 vreg (不含 phi incoming；phi use 属于前驱边) *)
let block_raw_uses (bb : basic_block) : IntSet.t =
  let instr_uses =
    List.concat_map
      (function
        | Phi _ -> []
        | instr -> instr_uses instr)
      bb.bb_instrs
  in
  vregs_of_values (instr_uses @ terminator_uses bb.bb_term)

(* 为每个函数做活变量分析 *)
let analyze (f : func) : liveness =
  let succs = successors f in

  (* 预计算每个块的 def / raw_use *)
  let def_map = ref IntMap.empty in
  let use_map = ref IntMap.empty in
  List.iter (fun (lbl, bb) ->
    def_map := IntMap.add lbl (block_defs bb) !def_map;
    use_map := IntMap.add lbl (block_raw_uses bb) !use_map
  ) f.f_blocks;

  (* 后继块 phi 的入边: 如果 B 的后继 S 中有 phi, 则该 phi 中来自 B 的源 vreg
     是 B 的额外 use *)
  let add_phi_uses () =
    List.iter (fun (lbl, _) ->
      let succ_set = try IntMap.find lbl succs with Not_found -> IntSet.empty in
      IntSet.iter (fun succ_lbl ->
        match List.find_opt (fun (l, _) -> l = succ_lbl) f.f_blocks with
        | None -> ()
        | Some (_, succ_bb) ->
          List.iter (fun instr ->
            match instr with
            | Phi { incoming; _ } ->
              List.iter (fun (v, pred) ->
                if pred = lbl then
                  use_map := IntMap.update lbl (fun prev ->
                    let s = match prev with None -> IntSet.empty | Some s -> s in
                    Some
                      (match v with
                       | VReg r -> IntSet.add r s
                       | Imm _ | Global _ -> s)
                  ) !use_map
              ) incoming
            | _ -> ()
          ) succ_bb.bb_instrs
      ) succ_set
    ) f.f_blocks
  in
  add_phi_uses ();

  (* 按 label 逆序遍历 *)
  let labels = List.map fst f.f_blocks in
  let rev_labels = List.rev labels in

  let live_in = ref IntMap.empty in
  let live_out = ref IntMap.empty in
  List.iter (fun lbl ->
    live_in := IntMap.add lbl IntSet.empty !live_in;
    live_out := IntMap.add lbl IntSet.empty !live_out
  ) labels;

  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun lbl ->
      let succ_set = try IntMap.find lbl succs with Not_found -> IntSet.empty in
      let new_out =
        IntSet.fold (fun succ acc ->
          IntSet.union acc (IntMap.find succ !live_in)
        ) succ_set IntSet.empty
      in
      if not (IntSet.equal new_out (IntMap.find lbl !live_out)) then begin
        live_out := IntMap.add lbl new_out !live_out;
        changed := true
      end;
      let use_set = IntMap.find lbl !use_map in
      let def_set = IntMap.find lbl !def_map in
      (* in = (use ∪ out) - def。不能写成 use ∪ (out - def)：
         block_raw_uses 收集的是“所有”use（含块内先 def 后 use），
         若不加 -def 会把这些块内定义的变量错误算进 live_in。 *)
      let new_in = IntSet.diff (IntSet.union use_set new_out) def_set in
      if not (IntSet.equal new_in (IntMap.find lbl !live_in)) then begin
        live_in := IntMap.add lbl new_in !live_in;
        changed := true
      end
    ) rev_labels
  done;
  { live_in = !live_in; live_out = !live_out }

(* 对整个 module 分析 *)
let analyze_module (m : module_) : (string * liveness) list =
  List.map (fun (name, f) -> (name, analyze f)) m.m_funcs
