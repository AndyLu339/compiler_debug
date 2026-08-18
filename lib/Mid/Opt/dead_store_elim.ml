(* ToyC 优化 — 死 store 消除
   当前只跟踪精确可识别的位置：alloca 栈槽与全局对象，并做一个更接近
   LLVM 语义的保守近似：
   - 函数返回后，只有当前函数的 alloca 栈槽对调用者不可见，因此可在
     function-exit 边界视为 dead；
   - 全局对象在函数返回后仍可被观察，因此在 exit 处必须视为 live；
   - call 作为对“可见内存”的 barrier 处理。由于 ToyC 无指针/取地址，
     被调用函数无法直接访问当前函数的 alloca 栈槽，所以这里仅把全局
     对象视为 call 可能读写的可见位置。 *)

open Ir_types

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)
module StringSet = Set.Make (String)
module LocOrd = struct
  type t =
    | StackSlot of int
    | GlobalSlot of string

  let compare = compare
end

module LocSet = Set.Make (LocOrd)

let loc_of_ptr (allocas : IntSet.t) (globals : StringSet.t) = function
  | VReg r when IntSet.mem r allocas -> Some (LocOrd.StackSlot r)
  | Global name when StringSet.mem name globals -> Some (LocOrd.GlobalSlot name)
  | _ -> None

let collect_allocas (f : func) : IntSet.t =
  List.fold_left (fun acc (_, bb) ->
    List.fold_left (fun acc instr ->
      match instr with
      | Alloca { dst; _ } -> IntSet.add dst acc
      | _ -> acc
    ) acc bb.bb_instrs
  ) IntSet.empty f.f_blocks

let collect_globals (m : module_) : StringSet.t =
  List.fold_left
    (fun acc -> function
      | GVar { name; _ } | GConst { name; _ } -> StringSet.add name acc)
    StringSet.empty m.m_globals

let successors (f : func) : IntSet.t IntMap.t =
  List.fold_left (fun acc (lbl, bb) ->
    match bb.bb_term with
    | Jump l       -> IntMap.add lbl (IntSet.of_list [ l ]) acc
    | Br (_, t, f) -> IntMap.add lbl (IntSet.of_list [ t; f ]) acc
    (* Ret 块无后继 → 不写入 map。这样数据流分析里 find_opt 返回 None，
       走 visible_locs 分支，把全局对象在函数出口视为 live。 *)
    | Ret _        -> acc
  ) IntMap.empty f.f_blocks

let block_use_def (allocas : IntSet.t) (globals : StringSet.t)
    (visible_locs : LocSet.t)
    (bb : basic_block) : LocSet.t * LocSet.t =
  List.fold_left (fun (use_set, def_set) instr ->
    match instr with
    | Load { ptr; _ } ->
        begin match loc_of_ptr allocas globals ptr with
        | Some p when not (LocSet.mem p def_set) -> (LocSet.add p use_set, def_set)
        | _ -> (use_set, def_set)
        end
    | Store { ptr; _ } ->
        begin match loc_of_ptr allocas globals ptr with
        | Some p -> (use_set, LocSet.add p def_set)
        | None -> (use_set, def_set)
        end
    | Call _ ->
        (LocSet.union use_set visible_locs, LocSet.union def_set visible_locs)
    | _ ->
        (use_set, def_set)
  ) (LocSet.empty, LocSet.empty) bb.bb_instrs

let run_on_func (globals : StringSet.t) (f : func) : func =
  let allocas = collect_allocas f in
  let all_locs =
    IntSet.fold (fun r acc -> LocSet.add (LocOrd.StackSlot r) acc) allocas LocSet.empty
    |> fun acc ->
    StringSet.fold (fun name acc -> LocSet.add (LocOrd.GlobalSlot name) acc) globals acc
  in
  let visible_locs =
    StringSet.fold (fun name acc -> LocSet.add (LocOrd.GlobalSlot name) acc) globals LocSet.empty
  in
  if LocSet.is_empty all_locs then f
  else
    let succs = successors f in
    let use_map = ref IntMap.empty in
    let def_map = ref IntMap.empty in
    List.iter (fun (lbl, bb) ->
      let use_set, def_set = block_use_def allocas globals visible_locs bb in
      use_map := IntMap.add lbl use_set !use_map;
      def_map := IntMap.add lbl def_set !def_map
    ) f.f_blocks;

    let live_in = ref IntMap.empty in
    let live_out = ref IntMap.empty in
    List.iter (fun (lbl, _) ->
      live_in := IntMap.add lbl LocSet.empty !live_in;
      live_out := IntMap.add lbl LocSet.empty !live_out
    ) f.f_blocks;

    let labels = List.rev (List.map fst f.f_blocks) in
    let changed = ref true in
    while !changed do
      changed := false;
      List.iter (fun lbl ->
        let succ_live =
          match IntMap.find_opt lbl succs with
            | None -> visible_locs
          | Some succ_set ->
              IntSet.fold (fun succ acc ->
                  LocSet.union acc (IntMap.find succ !live_in)
                ) succ_set LocSet.empty
        in
          if not (LocSet.equal succ_live (IntMap.find lbl !live_out)) then begin
          live_out := IntMap.add lbl succ_live !live_out;
          changed := true
        end;
        let use_set = IntMap.find lbl !use_map in
        let def_set = IntMap.find lbl !def_map in
          let in_set = LocSet.union use_set (LocSet.diff succ_live def_set) in
          if not (LocSet.equal in_set (IntMap.find lbl !live_in)) then begin
          live_in := IntMap.add lbl in_set !live_in;
          changed := true
        end
      ) labels
    done;

    let changed = ref false in
    let new_blocks = List.map (fun (lbl, bb) ->
      let live = ref (IntMap.find lbl !live_out) in
      let new_instrs =
        List.fold_left (fun acc instr ->
          match instr with
          | Load { ptr; _ } ->
                begin match loc_of_ptr allocas globals ptr with
                | Some p -> live := LocSet.add p !live
              | None -> ()
              end;
              instr :: acc
          | Store ({ ptr; _ } as s) ->
                begin match loc_of_ptr allocas globals ptr with
                | Some p when not (LocSet.mem p !live) ->
                  changed := true;
                  acc
              | Some p ->
                    live := LocSet.remove p !live;
                  Store s :: acc
              | None ->
                  Store s :: acc
              end
            | Call _ ->
                live := LocSet.union !live visible_locs;
                instr :: acc
          | _ ->
              instr :: acc
        ) [] (List.rev bb.bb_instrs)
      in
      (lbl, { bb with bb_instrs = new_instrs })
    ) f.f_blocks in
    if !changed then { f with f_blocks = new_blocks } else f

let run (m : module_) : module_ =
  let globals = collect_globals m in
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func globals f)) m.m_funcs }
