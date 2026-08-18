(* ToyC 优化 — 全局死代码消除 (LLVM: -globaldce)
   删除从 main 不可达的函数, 以及未被任何可达函数引用的全局变量/常量。 *)

open Ir_types

module StringSet = Set.Make (String)
module StringMap = Map.Make (String)

(* 收集 value 中引用的全局名 *)
let add_global (acc : StringSet.t) (v : value) : StringSet.t =
  match v with
  | Global name -> StringSet.add name acc
  | VReg _ | Imm _ -> acc

(* 收集函数体内所有被引用的全局名 *)
let globals_of_func (f : func) : StringSet.t =
  List.fold_left (fun acc (_, bb) ->
    let acc =
      List.fold_left (fun acc i ->
        List.fold_left add_global acc (instr_uses i)
      ) acc bb.bb_instrs
    in
    List.fold_left add_global acc (terminator_uses bb.bb_term)
  ) StringSet.empty f.f_blocks

(* 收集函数体内所有被调用的函数名 *)
let callees_of_func (f : func) : StringSet.t =
  List.fold_left (fun acc (_, bb) ->
    List.fold_left (fun acc -> function
      | Call { fn; _ } -> StringSet.add fn acc
      | _ -> acc
    ) acc bb.bb_instrs
  ) StringSet.empty f.f_blocks

let run (m : module_) : module_ =
  let func_map =
    List.fold_left (fun acc (name, f) -> StringMap.add name f acc)
      StringMap.empty m.m_funcs
  in

  (* 1. 调用图可达性: 从 main 出发 BFS。
        若没有 main (理论上不会发生), 保守地保留所有函数。 *)
  let roots =
    if StringMap.mem "main" func_map then [ "main" ]
    else List.map fst m.m_funcs
  in
  let reachable =
    let rec visit visited = function
      | [] -> visited
      | name :: rest ->
          if StringSet.mem name visited then visit visited rest
          else
            let visited = StringSet.add name visited in
            let callees =
              match StringMap.find_opt name func_map with
              | Some f -> StringSet.elements (callees_of_func f)
              | None -> []
            in
            visit visited (callees @ rest)
    in
    visit StringSet.empty roots
  in

  (* 2. 可达函数引用的全局变量 *)
  let used_globals =
    StringSet.fold (fun name acc ->
      match StringMap.find_opt name func_map with
      | Some f -> StringSet.union acc (globals_of_func f)
      | None -> acc
    ) reachable StringSet.empty
  in

  (* 3. 过滤: 保留可达函数与被引用的全局变量 (保持原有顺序) *)
  let funcs =
    List.filter (fun (name, _) -> StringSet.mem name reachable) m.m_funcs
  in
  let globals =
    List.filter (fun g ->
      let name = match g with GVar { name; _ } | GConst { name; _ } -> name in
      StringSet.mem name used_globals
    ) m.m_globals
  in

  { m_globals = globals; m_funcs = funcs }
