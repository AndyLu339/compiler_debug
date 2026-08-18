(* ToyC 优化 — 跳转穿透 (Jump Threading)
   1. 无条件穿透: A → B → C, B 只有 Jump C 且无 phi → A → C
   2. 条件分支穿透: B 有 Br(cond, C, D), 可证明 cond=0/≠0 → 直接跳转 *)

open Ir_types

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

(* ---- 值确定性分析 ------------------------------------------------------ *)

type known = KnownZero | KnownNonZero

(* 跟随 Copy/Zext 链, 尝试判定一个 vreg 是否确定为 0 或非 0 *)
let rec determine (defs : instr IntMap.t) (v : value) : known option =
  match v with
  | Imm 0 -> Some KnownZero
  | Imm _ -> Some KnownNonZero
  | Global _ -> None
  | VReg r ->
    match IntMap.find_opt r defs with
    | None -> None
    | Some (Copy { src; _ } | Zext { src; _ }) ->
      determine defs src
    | Some (Icmp { cond = IEq; lhs = VReg x; rhs = VReg y; _ }) when x = y ->
      Some KnownNonZero
    | Some (Icmp { cond = INe; lhs = VReg x; rhs = VReg y; _ }) when x = y ->
      Some KnownZero
    | Some (Binop { op = Eq; lhs = VReg x; rhs = VReg y; _ }) when x = y ->
      Some KnownNonZero
    | Some (Binop { op = Ne; lhs = VReg x; rhs = VReg y; _ }) when x = y ->
      Some KnownZero
    | Some (Binop { op = Sub; lhs = VReg x; rhs = VReg y; _ }) when x = y ->
      Some KnownZero
    | Some (Binop { op = Add; lhs = Imm a; rhs = Imm b; _ }) ->
      if a + b = 0 then Some KnownZero else Some KnownNonZero
    | Some (Binop { op = Sub; lhs = Imm a; rhs = Imm b; _ }) ->
      if a - b = 0 then Some KnownZero else Some KnownNonZero
    | _ -> None

(* ---- 辅助: 构建 def map 和前驱 map ------------------------------------ *)

let build_def_map (bmap : basic_block IntMap.t) : instr IntMap.t =
  IntMap.fold (fun _ bb m ->
    List.fold_left (fun m instr ->
      match instr_dst instr with
      | Some dst -> IntMap.add dst instr m
      | None -> m
    ) m bb.bb_instrs
  ) bmap IntMap.empty

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

let has_phi (bb : basic_block) =
  List.exists (function Phi _ -> true | _ -> false) bb.bb_instrs

(* ---- 主逻辑 ------------------------------------------------------------ *)

(* 单前驱穿透: (v, old_lbl) → (v, new_lbl) 标签重映射 *)
let remap_phi_labels (remap : label IntMap.t) (bmap : basic_block IntMap.t) =
  IntMap.map (fun bb ->
    { bb with bb_instrs = List.map (fun instr ->
      match instr with
      | Phi { dst; incoming } ->
        Phi { dst; incoming = List.map (fun (v, lbl) ->
          match IntMap.find_opt lbl remap with
          | Some new_lbl -> (v, new_lbl)
          | None -> (v, lbl)
        ) incoming }
      | _ -> instr
    ) bb.bb_instrs }
  ) bmap

(* 多前驱穿透: 为 successor 的 phi 节点补充来自新前驱的条目 *)
let add_phi_entries (adds : (label * label * label) list)
    (bmap : basic_block IntMap.t) =
  (* adds: (succ_block, target_label, new_label) — 在 succ_block 的 phi 里,
     对每个 (v, target_label), 增加 (v, new_label) *)
  let by_succ = List.fold_left (fun m (succ, target, new_lbl) ->
    IntMap.update succ (fun prev ->
      let lst = match prev with Some l -> l | None -> [] in
      Some ((target, new_lbl) :: lst)
    ) m
  ) IntMap.empty adds in
  IntMap.mapi (fun lbl bb ->
    match IntMap.find_opt lbl by_succ with
    | None -> bb
    | Some mappings ->
      { bb with bb_instrs = List.map (fun instr ->
        match instr with
        | Phi { dst; incoming } ->
          let extras = List.concat_map (fun (target_lbl, new_lbl) ->
            List.filter_map (fun (v, lbl) ->
              if lbl = target_lbl then Some (v, new_lbl) else None
            ) incoming
          ) mappings in
          Phi { dst; incoming = incoming @ extras }
        | _ -> instr
      ) bb.bb_instrs }
  ) bmap

let run_on_func (f : func) : func =
  let block_map =
    List.fold_left (fun m (l, bb) -> IntMap.add l bb m) IntMap.empty f.f_blocks
  in

  let rec fixpoint (bmap : basic_block IntMap.t) : basic_block IntMap.t =
    let defs = build_def_map bmap in
    let preds = compute_preds bmap in
    let changed = ref false in
    let phi_remap = ref IntMap.empty in
    let phi_adds : (label * label * label) list ref = ref [] in

    let bmap = IntMap.map (fun bb ->
      match bb.bb_term with
      | Br (cond, t_lbl, f_lbl) ->
        begin match determine defs cond with
        | Some KnownNonZero ->
          changed := true;
          { bb with bb_term = Jump t_lbl }
        | Some KnownZero ->
          changed := true;
          { bb with bb_term = Jump f_lbl }
        | None -> bb
        end
      | Jump target ->
        begin match IntMap.find_opt target bmap with
        | Some target_bb
          when target_bb.bb_instrs = []
            && target <> target_bb.bb_label ->
          begin match target_bb.bb_term with
          | Jump final when final <> bb.bb_label ->
            let target_preds =
              match IntMap.find_opt target preds with
              | Some p -> p | None -> IntSet.empty in
            if IntSet.cardinal target_preds = 1 then begin
              changed := true;
              phi_remap := IntMap.add target bb.bb_label !phi_remap;
              { bb with bb_term = Jump final }
            end else if not (has_phi target_bb) then begin
              changed := true;
              phi_adds := (final, target, bb.bb_label) :: !phi_adds;
              { bb with bb_term = Jump final }
            end else bb
          | _ -> bb
          end
        | _ -> bb
        end
      | _ -> bb
    ) bmap in

    if !changed then
      let bmap = remap_phi_labels !phi_remap bmap in
      let bmap = add_phi_entries !phi_adds bmap in
      let reachable = compute_reachable bmap f.f_entry in
      let bmap = IntMap.filter (fun l _ -> IntSet.mem l reachable) bmap in
      let preds = compute_preds bmap in
      let bmap = fix_phis bmap preds in
      fixpoint bmap
    else
      bmap

  and compute_reachable (bmap : basic_block IntMap.t) (entry : label) : IntSet.t =
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

  and fix_phis (bmap : basic_block IntMap.t) (preds : IntSet.t IntMap.t) =
    IntMap.map (fun bb ->
      let my_preds = match IntMap.find_opt bb.bb_label preds with
        | Some p -> p | None -> IntSet.empty in
      let new_instrs = List.filter_map (fun instr ->
        match instr with
        | Phi { dst; incoming } ->
          let new_incoming = List.filter (fun (_, lbl) ->
            IntSet.mem lbl my_preds
          ) incoming in
          begin match new_incoming with
          | [] -> None
          | _ -> Some (Phi { dst; incoming = new_incoming })
          end
        | _ -> Some instr
      ) bb.bb_instrs in
      { bb with bb_instrs = new_instrs }
    ) bmap
  in

  let new_bmap = fixpoint block_map in
  { f with f_blocks = IntMap.bindings new_bmap
                     |> List.sort (fun (a,_) (b,_) -> compare a b) }

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
