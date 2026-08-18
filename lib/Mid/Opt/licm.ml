(* ToyC 优化 — 循环不变量外提 (LICM)
   在 SSA 上做:
   1. 识别自然循环 (复用 loop_info)
   2. 迭代标记循环不变量指令 (纯运算, 操作数全来自循环外或已标记不变)
   3. 外提到 preheader
   从最内层循环向外处理 *)

open Ir_types
open Loop_info

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)
module VMap   = Map.Make (Int)
module VSet   = Set.Make (Int)

type loop_memory = {
  stored_ptrs : value list;
  has_call : bool;
}

(* ---- 判断是否有副作用 (不可外提) ----------------------------------- *)

let has_side_effect (i : instr) : bool =
  match i with
  | Store _ | Call _ | Alloca _ | Phi _ | Load _ -> true
  | _ -> false

let collect_loop_memory (bmap : basic_block IntMap.t) (loop_blocks : IntSet.t)
    : loop_memory =
  let stored_ptrs = ref [] in
  let has_call = ref false in
  IntSet.iter (fun lbl ->
    let bb = IntMap.find lbl bmap in
    List.iter (function
      | Store { ptr; _ } ->
          stored_ptrs := ptr :: !stored_ptrs
      | Call _ ->
          has_call := true
      | _ ->
          ()
    ) bb.bb_instrs
  ) loop_blocks;
  { stored_ptrs = !stored_ptrs; has_call = !has_call }

let can_hoist_load (mem : loop_memory) (ptr : value) : bool =
  (* LLVM 的 LICM 依赖 alias/mod-ref 分析来判定 load 是否可外提。
     这里没有 AA，因此只接受一个更保守的子集：
     1. 循环内没有 call
     2. 循环内没有对“同一地址值”的 store *)
  (not mem.has_call)
  && not (List.exists (fun stored_ptr -> compare stored_ptr ptr = 0) mem.stored_ptrs)

let is_hoistable (mem : loop_memory) (instr : instr) : bool =
  match instr with
  | Load { ptr; _ } -> can_hoist_load mem ptr
  | _ -> not (has_side_effect instr)

(* ---- 检查 operands 是否全是不变量 -------------------------------- *)

let operands_invariant (uses : value list) (def_site : int VMap.t)
    (loop_blocks : IntSet.t) (inv_vregs : VSet.t) : bool =
  List.for_all (fun v -> match v with
    | Imm _ | Global _ -> true
    | VReg r ->
        (match VMap.find_opt r def_site with
         | Some def_blk when IntSet.mem def_blk loop_blocks ->
             VSet.mem r inv_vregs
         | _ -> true)
  ) uses

(* ---- 构建 def-site map ----------------------------------------------- *)

let build_def_site (f : func) (bmap : basic_block IntMap.t) : int VMap.t =
  let def_site = ref VMap.empty in
  List.iter (fun (_, vreg) -> def_site := VMap.add vreg f.f_entry !def_site) f.f_params;
  IntMap.iter (fun lbl bb ->
    List.iter (fun instr ->
      match instr_dst instr with
      | Some dst -> def_site := VMap.add dst lbl !def_site
      | None -> ()
    ) bb.bb_instrs
  ) bmap;
  !def_site

(* ---- 迭代发现循环不变量 -------------------------------------------------- *)

let discover_invariants (bmap : basic_block IntMap.t) (loop_blocks : IntSet.t)
    (def_site : int VMap.t) : VSet.t =
  let loop_mem = collect_loop_memory bmap loop_blocks in
  let inv_vregs = ref VSet.empty in
  let changed = ref true in
  while !changed do
    changed := false;
    IntSet.iter (fun lbl ->
      let bb = IntMap.find lbl bmap in
      List.iter (fun instr ->
        let dst_opt = instr_dst instr in
        match dst_opt with
        | None -> ()
        | Some dst when VSet.mem dst !inv_vregs -> ()
          | Some _ when not (is_hoistable loop_mem instr) -> ()
        | Some dst ->
            let uses = instr_uses instr in
            if operands_invariant uses def_site loop_blocks !inv_vregs then begin
              inv_vregs := VSet.add dst !inv_vregs;
              changed := true
            end
      ) bb.bb_instrs
    ) loop_blocks
  done;
  !inv_vregs

(* ---- 外提到 preheader ---------------------------------------------------- *)

let hoist (bmap : basic_block IntMap.t) (loop_blocks : IntSet.t)
    (preheader : label) (inv_vregs : VSet.t) : basic_block IntMap.t =
  (* 1. 按块标号顺序收集外提指令 *)
  let hoisted = ref [] in
  IntSet.iter (fun lbl ->
    let bb = IntMap.find lbl bmap in
    List.iter (fun instr ->
      match instr_dst instr with
      | Some dst when VSet.mem dst inv_vregs -> hoisted := instr :: !hoisted
      | _ -> ()
    ) bb.bb_instrs
  ) loop_blocks;
  let hoisted = List.rev !hoisted in

  (* 2. 从循环体中移除 *)
  let bmap = IntMap.map (fun bb ->
    if IntSet.mem bb.bb_label loop_blocks then
      let new_instrs = List.filter (fun instr ->
        match instr_dst instr with
        | Some dst -> not (VSet.mem dst inv_vregs)
        | None -> true
      ) bb.bb_instrs in
      { bb with bb_instrs = new_instrs }
    else bb
  ) bmap in

  (* 3. 插入到 preheader 末尾 *)
  let pre_bb = IntMap.find preheader bmap in
  let new_instrs = pre_bb.bb_instrs @ hoisted in
  IntMap.add preheader { pre_bb with bb_instrs = new_instrs } bmap

(* ---- 单函数 -------------------------------------------------------------- *)

let run_on_func (f : func) : func =
  let dom = Dominance.analyze f in
  let li = analyze f dom in
  if li.loops = [] then f
  else
    let bmap = List.fold_left (fun m (l, bb) -> IntMap.add l bb m)
        IntMap.empty f.f_blocks in

    (* 最内层循环优先 *)
    let loops = List.sort (fun a b -> compare b.depth a.depth) li.loops in

    let bmap = List.fold_left (fun bmap loop ->
      match loop.preheader with
      | None -> bmap
      | Some preheader ->
          let def_site = build_def_site f bmap in
          let inv = discover_invariants bmap loop.blocks def_site in
          if VSet.is_empty inv then bmap
          else hoist bmap loop.blocks preheader inv
    ) bmap loops in

    { f with f_blocks = IntMap.bindings bmap |> List.sort (fun (a,_) (b,_) -> compare a b) }

(* ---- 入口 ---------------------------------------------------------------- *)

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
