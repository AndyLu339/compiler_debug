(* ToyC 优化 — 死参数消除 (LLVM: -deadargelim)

   删除从未被函数体使用的形参，并同步更新所有调用点的实参列表。 *)

open Ir_types

module IntSet = Set.Make (Int)
module StringMap = Map.Make (String)

(* 收集函数体中实际被使用到的形参 vreg 集合。 *)
let used_param_vregs (f : func) : IntSet.t =
  let used = ref IntSet.empty in
  let add_uses uses =
    List.iter (function
      | VReg r -> used := IntSet.add r !used
      | Imm _ | Global _ -> ())
      uses
  in
  List.iter (fun (_, bb) ->
    List.iter (fun instr -> add_uses (instr_uses instr)) bb.bb_instrs;
    add_uses (terminator_uses bb.bb_term)
  ) f.f_blocks;
  !used

(* 返回与 f.f_params 对齐的保留标志列表。 *)
let kept_flags (f : func) : bool list =
  let used = used_param_vregs f in
  List.map (fun (_, r) -> IntSet.mem r used) f.f_params

(* 按保留标志过滤调用实参。 *)
let filter_args_by_flags (args : value list) (flags : bool list) : value list =
  let rec go args flags acc =
    match args, flags with
    | [], _ -> List.rev acc
    | _, [] -> List.rev acc
    | a :: at, true :: ft -> go at ft (a :: acc)
    | _ :: at, false :: ft -> go at ft acc
  in
  go args flags []

(* 模块入口：删除死形参并同步更新所有调用点。 *)
let run (m : module_) : module_ =
  let flag_map =
    List.fold_left (fun m (name, f) ->
      StringMap.add name (kept_flags f) m
    ) StringMap.empty m.m_funcs
  in

  let update_func (name, f) =
    let flags = StringMap.find name flag_map in
    let new_params =
      let rec keep params flags acc =
        match params, flags with
        | [], _ -> List.rev acc
        | _, [] -> List.rev acc
        | p :: pt, true :: ft -> keep pt ft (p :: acc)
        | _ :: pt, false :: ft -> keep pt ft acc
      in
      keep f.f_params flags []
    in
    let new_blocks =
      List.map (fun (lbl, bb) ->
        let new_instrs =
          List.map (function
            | Call c ->
                let callee_flags =
                  match StringMap.find_opt c.fn flag_map with
                  | Some fl -> fl
                  | None -> List.map (fun _ -> true) c.args
                in
                Call { c with args = filter_args_by_flags c.args callee_flags }
            | i -> i
          ) bb.bb_instrs
        in
        (lbl, { bb with bb_instrs = new_instrs })
      ) f.f_blocks
    in
    (name, { f with f_params = new_params; f_blocks = new_blocks })
  in

  { m with m_funcs = List.map update_func m.m_funcs }
