(* ToyC 优化 — 循环分支外提 (LLVM: -simple-loop-unswitch)

   找到循环体中条件为循环不变量的分支，把整个循环克隆成 true/false 两个版本，
   并在 preheader 里用原不变条件选择进入哪个版本。 *)

open Ir_types
open Loop_info

module U = Loop_unroll
module IntMap = U.IntMap
module IntSet = U.IntSet

(* 构建 label -> basic_block 映射。 *)
let build_bmap (f : func) : basic_block IntMap.t =
  U.build_bmap f

(* 返回终结指令的后继标号。 *)
let term_succs = function
  | Jump l -> [ l ]
  | Br (_, t, f) -> [ t; f ]
  | Ret _ -> []

(* 设置指令的 dst vreg，用于克隆时重编号。 *)
let set_instr_dst (dst : int) (i : instr) : instr =
  match i with
  | Alloca a -> Alloca { a with dst }
  | Load l -> Load { l with dst }
  | Binop b -> Binop { b with dst }
  | Icmp c -> Icmp { c with dst }
  | Call c -> Call { c with dst = Some dst }
  | Phi p -> Phi { p with dst }
  | Shl s -> Shl { s with dst }
  | AShr s -> AShr { s with dst }
  | And a -> And { a with dst }
  | Zext z -> Zext { z with dst }
  | Copy c -> Copy { c with dst }
  | Store _ -> failwith "set_instr_dst: store has no dst"

(* 根据 vreg 映射重写 value。 *)
let remap_value (vmap : int IntMap.t) (v : value) : value =
  match v with
  | VReg r ->
      (match IntMap.find_opt r vmap with Some r' -> VReg r' | None -> v)
  | Imm _ | Global _ -> v

(* 重写指令 operands 中的 vreg，并保留原 dst。 *)
let remap_instr_uses (vmap : int IntMap.t) (i : instr) : instr =
  let f r = Option.map (fun r' -> VReg r') (IntMap.find_opt r vmap) in
  U.map_instr_values f i

(* 在循环体中寻找条件为循环不变量的可外提分支。 *)
let find_unswitch_branch (f : func) (bmap : basic_block IntMap.t) (lp : loop)
    : (label * value * label * label) option =
  let du = Ir_analysis.build_def_use { m_globals = []; m_funcs = [ (f.f_name, f) ] } in
  let is_invariant v =
    match v with
    | Imm _ | Global _ -> true
    | VReg r ->
        (match Ir_analysis.VMap.find_opt r du.def_site with
         | None -> true
         | Some (lbl, _) -> not (IntSet.mem lbl lp.blocks))
  in
  let labels = IntSet.elements lp.blocks in
  List.find_map (fun lbl ->
    if lbl = lp.header then None
    else
      let bb = IntMap.find lbl bmap in
      match bb.bb_term with
      | Br (cond, t, f) when t <> f && is_invariant cond ->
          Some (lbl, cond, t, f)
      | _ -> None
  ) labels

(* 为循环的每个旧 label 分配 true/false 两个克隆 label。 *)
let build_clone_label_maps (loop_labels : label list) (fresh_label : unit -> int)
    : int IntMap.t * int IntMap.t =
  let true_lmap =
    List.fold_left (fun m l -> IntMap.add l (fresh_label ()) m) IntMap.empty loop_labels
  in
  let false_lmap =
    List.fold_left (fun m l -> IntMap.add l (fresh_label ()) m) IntMap.empty loop_labels
  in
  (true_lmap, false_lmap)

(* 为循环中每个 vreg 分配 true/false 两个克隆 vreg。 *)
let build_clone_vreg_maps (bmap : basic_block IntMap.t) (loop_labels : label list)
    (fresh_vreg : unit -> int) : int IntMap.t * int IntMap.t =
  let build_one () =
    List.fold_left (fun m l ->
      let bb = IntMap.find l bmap in
      List.fold_left (fun m instr ->
        match instr_dst instr with
        | Some dst -> IntMap.add dst (fresh_vreg ()) m
        | None -> m
      ) m bb.bb_instrs
    ) IntMap.empty loop_labels
  in
  (build_one (), build_one ())

(* 克隆后修复退出块及其后继 phi 对旧 loop vreg 的引用。 *)
let rewrite_outside_uses (bmap : basic_block IntMap.t) (orig_bmap : basic_block IntMap.t)
    (loop_labels : label list) (lp : loop) (true_lmap : int IntMap.t)
    (false_lmap : int IntMap.t) (true_vmap : int IntMap.t) (false_vmap : int IntMap.t)
    (fresh_vreg : unit -> int) : basic_block IntMap.t =
  let loop_defs =
    List.fold_left (fun s lbl ->
      let bb = IntMap.find lbl orig_bmap in
      List.fold_left (fun s instr ->
        match instr_dst instr with
        | Some d -> IntSet.add d s
        | None -> s)
        s bb.bb_instrs
    ) IntSet.empty loop_labels
  in
  let clone_labels =
    IntMap.fold (fun _ l acc -> IntSet.add l acc) true_lmap
      (IntMap.fold (fun _ l acc -> IntSet.add l acc) false_lmap IntSet.empty)
  in
  let label_of side l =
    if IntSet.mem l lp.blocks then
      if side then IntMap.find l true_lmap else IntMap.find l false_lmap
    else l
  in
  let value_of side v =
    let vmap = if side then true_vmap else false_vmap in
    remap_value vmap v
  in
  let succ_phi_uses_for bb_label =
    let bb = IntMap.find bb_label bmap in
    List.fold_left (fun acc succ ->
      match IntMap.find_opt succ bmap with
      | None -> acc
      | Some sbb ->
          List.fold_left (fun acc instr ->
            match instr with
            | Phi p ->
                List.fold_left (fun acc (v, pred) ->
                  if pred = bb_label then
                    match v with
                    | VReg r -> IntSet.add r acc
                    | Imm _ | Global _ -> acc
                  else acc)
                  acc p.incoming
            | _ -> acc)
            acc sbb.bb_instrs)
      IntSet.empty (term_succs bb.bb_term)
  in
  let inserted = ref [] in
  let bmap =
    IntMap.map (fun bb ->
      if IntSet.mem bb.bb_label clone_labels then bb
      else
        let updated_existing_phis =
          List.map (function
            | Phi p ->
                let expanded =
                  List.concat_map (fun (v, pred) ->
                    if IntSet.mem pred lp.blocks then
                      [ (value_of true v, label_of true pred);
                        (value_of false v, label_of false pred) ]
                    else [ (v, pred) ]
                  ) p.incoming
                in
                let seen = ref IntSet.empty in
                let incoming =
                  List.filter (fun (_, l) ->
                    if IntSet.mem l !seen then false
                    else (seen := IntSet.add l !seen; true)
                  ) expanded
                in
                Phi { p with incoming }
            | i -> i
          ) bb.bb_instrs
        in
        let non_phi_vregs =
          List.fold_left (fun s v ->
            match v with
            | VReg r -> IntSet.add r s
            | Imm _ | Global _ -> s)
            IntSet.empty
            (List.concat_map (fun instr ->
              match instr with
              | Phi _ -> []
              | i -> instr_uses i)
              updated_existing_phis
             @ terminator_uses bb.bb_term)
        in
        let succ_phi_uses = succ_phi_uses_for bb.bb_label in
        let needed =
          IntSet.inter
            (IntSet.union non_phi_vregs succ_phi_uses)
            loop_defs
        in
        let missing =
          IntSet.filter (fun r ->
            not (List.exists (function
              | Phi { dst; _ } -> dst = r
              | _ -> false) updated_existing_phis))
            needed
        in
        IntSet.fold (fun r acc ->
          let preds =
            List.filter (fun x ->
              List.mem bb.bb_label (term_succs (IntMap.find x orig_bmap).bb_term))
              loop_labels
          in
          let r' = fresh_vreg () in
          inserted := (bb.bb_label, r, r') :: !inserted;
          let incoming =
            List.concat_map (fun pred ->
              [ (value_of true (VReg r), label_of true pred);
                (value_of false (VReg r), label_of false pred) ])
              preds
          in
          let phi = Phi { dst = r'; incoming } in
          let replace_instr = function
            | Phi _ as i -> i
            | i -> U.map_instr_values (fun x ->
                if x = r then Some (VReg r') else None) i
          in
          let instrs = phi :: List.map replace_instr acc.bb_instrs in
          let term =
            U.map_term_values (fun x ->
              if x = r then Some (VReg r') else None) acc.bb_term
          in
          { acc with bb_instrs = instrs; bb_term = term })
        missing { bb with bb_instrs = updated_existing_phis }
    ) bmap
  in
  IntMap.mapi (fun _lbl bb ->
    let instrs = List.map (function
      | Phi p ->
          let incoming =
            List.map (fun (v, pred) ->
              match v with
              | VReg r ->
                  (match List.find_opt (fun (e_lbl, old_r, _) ->
                     e_lbl = pred && old_r = r) !inserted with
                   | Some (_, _, r') -> (VReg r', pred)
                   | None -> (v, pred))
              | Imm _ | Global _ -> (v, pred))
              p.incoming
          in
          Phi { p with incoming }
      | i -> i) bb.bb_instrs in
    { bb with bb_instrs = instrs }) bmap

(* 对单个循环执行分支外提克隆；失败返回 None。 *)
let apply_unswitch (f : func) (bmap : basic_block IntMap.t) (lp : loop)
    : (basic_block IntMap.t * int * int) option =
  match lp.preheader with
  | None -> None
  | Some preheader ->
      let preheader_bb = IntMap.find preheader bmap in
      begin match preheader_bb.bb_term with
      | Jump target when target = lp.header ->
          let branch_opt = find_unswitch_branch f bmap lp in
          begin match branch_opt with
          | None -> None
          | Some (branch_lbl, cond, _t_lbl, _f_lbl) ->
              if IntMap.exists (fun lbl bb ->
                not (IntSet.mem lbl lp.blocks) && lbl <> preheader
                && List.exists (fun s -> IntSet.mem s lp.blocks) (term_succs bb.bb_term))
                bmap
              then None
              else begin
                let next_label = ref (f.f_max_label + 1) in
                let next_vreg = ref (f.f_max_vreg + 1) in
                let fresh_label () = let x = !next_label in incr next_label; x in
                let fresh_vreg () = let x = !next_vreg in incr next_vreg; x in

                let loop_labels = IntSet.elements lp.blocks in

                let true_lmap, false_lmap =
                  build_clone_label_maps loop_labels fresh_label in
                let true_vmap, false_vmap =
                  build_clone_vreg_maps bmap loop_labels fresh_vreg in

                let label_of side l =
                  if IntSet.mem l lp.blocks then
                    if side then IntMap.find l true_lmap else IntMap.find l false_lmap
                  else l
                in
                let value_of side v =
                  let vmap = if side then true_vmap else false_vmap in
                  remap_value vmap v
                in

                let clone_instr side instr =
                  let vmap = if side then true_vmap else false_vmap in
                  match instr with
                  | Phi p ->
                      let incoming =
                        List.map (fun (v, pred) ->
                          (value_of side v, label_of side pred)) p.incoming
                      in
                      Phi { dst = IntMap.find p.dst vmap; incoming }
                  | _ ->
                      let mapped = remap_instr_uses vmap instr in
                      (match instr_dst instr with
                       | Some old_dst ->
                           set_instr_dst (IntMap.find old_dst vmap) mapped
                       | None -> mapped)
                in

                let clone_term side bb_label =
                  function
                  | Ret v -> Ret (Option.map (value_of side) v)
                  | Jump l -> Jump (label_of side l)
                  | Br (cond, t_lbl, f_lbl) ->
                      if bb_label = branch_lbl then
                        if side then Jump (label_of side t_lbl)
                        else Jump (label_of side f_lbl)
                      else
                        Br (value_of side cond, label_of side t_lbl, label_of side f_lbl)
                in

                let clones =
                  List.concat_map (fun side ->
                    List.map (fun lbl ->
                      let bb = IntMap.find lbl bmap in
                      let new_lbl = label_of side lbl in
                      let new_bb =
                        { bb_label = new_lbl;
                          bb_instrs = List.map (clone_instr side) bb.bb_instrs;
                          bb_term = clone_term side lbl bb.bb_term }
                      in
                      (new_lbl, new_bb)
                    ) loop_labels
                  ) [ true; false ]
                in

                let new_preheader =
                  { preheader_bb with
                    bb_term = Br (cond, label_of true lp.header, label_of false lp.header) }
                in

                let orig_bmap = bmap in
                let bmap =
                  IntMap.fold (fun lbl _ acc ->
                    if IntSet.mem lbl lp.blocks then acc
                    else IntMap.add lbl (IntMap.find lbl bmap) acc
                  ) bmap IntMap.empty
                in
                let bmap = IntMap.add preheader new_preheader bmap in
                let bmap = List.fold_left (fun m (l, bb) -> IntMap.add l bb m) bmap clones in

                let bmap =
                  rewrite_outside_uses bmap orig_bmap loop_labels lp
                    true_lmap false_lmap true_vmap false_vmap fresh_vreg
                in
                Some (bmap, !next_label - 1, !next_vreg - 1)
              end
          end
      | _ -> None
      end

(* 逐函数反复执行 loop unswitch。 *)
let run_on_func (f : func) : func =
  let rec fixpoint (f : func) : func =
    let bmap = build_bmap f in
    let dom = Dominance.analyze f in
    let li = analyze f dom in
    let loops =
      List.sort (fun a b ->
        let c = compare b.depth a.depth in
        if c <> 0 then c else compare a.header b.header
      ) li.loops
    in
    match List.find_map (apply_unswitch f bmap) loops with
    | None -> f
    | Some (bmap', new_max_label, new_max_vreg) ->
        fixpoint
          { f with
            f_blocks =
              IntMap.bindings bmap'
              |> List.sort (fun (a, _) (b, _) -> compare a b);
            f_max_label = new_max_label;
            f_max_vreg = new_max_vreg }
  in
  fixpoint f

(* 模块入口。 *)
let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
