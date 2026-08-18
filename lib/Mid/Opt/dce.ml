(* ToyC 优化 — 死代码消除
   基于 def-use: 无 uses 的 vreg 删除其定义指令（无副作用指令） *)

open Ir_types

let has_side_effect = function
  | Store _ | Call _ -> true
  | _ -> false

let run_on_func (f : func) : func =
  let rec fixpoint (f : func) : func =
    let du = Ir_analysis.build_def_use { m_globals = []; m_funcs = [ (f.f_name, f) ] } in
    let changed = ref false in
    let new_blocks = List.map (fun (lbl, bb) ->
      let new_instrs = List.filter (fun instr ->
        match instr_dst instr with
        | None -> true
        | Some _ when has_side_effect instr -> true
        | Some dst ->
            let live = Ir_analysis.VMap.mem dst du.use_sites in
            if live then true else (changed := true; false)
      ) bb.bb_instrs in
      (lbl, { bb with bb_instrs = new_instrs })
    ) f.f_blocks in
    let f' = { f with f_blocks = new_blocks } in
    if !changed then fixpoint f' else f'
  in
  fixpoint f

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
