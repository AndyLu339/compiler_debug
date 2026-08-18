(* ToyC 寄存器分配 — 线性扫描 *)

open Ir_types
open Live_intervals

module IntMap = Map.Make (Int)
module IntSet = Set.Make (Int)
module StringMap = Map.Make (String)

(* ---- 可用寄存器 ---- *)

(* 参考 LLVM ，是否保存/恢复哪些寄存器应在“看过整个函数”之后决定。
   这里保守地按函数是否包含 call 来区分寄存器池：
   - leaf 函数（无 call）使用全部 caller-saved：t0-t4 + a0-a7。
     a0-a7 在参数被 emit_params 挪走后即可复用；leaf 无 call，不会破坏传参/返回值。
     但参数 vreg 本身只分配到 t0-t4（见 leaf_param_limit），
     避免与 a0-a7 参数传入寄存器产生拷贝顺序冲突。
   - 非 leaf 函数继续优先使用 callee-saved，避免跨 call 活跃值被 clobber。 *)
let leaf_regs =
  [| "t0"; "t1"; "t2"; "t3"; "t4";
     "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |]
let nonleaf_regs =
  [| "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11" |]

(* leaf 函数中参数 vreg 只允许分配到前 leaf_param_limit 个寄存器（t0-t4），
   因为函数入口时参数值仍在 a0-a7；若把参数 vreg 也放进 a0-a7，
   emit_params 顺序拷贝时会提前覆盖尚未读取的源寄存器。 *)
let leaf_param_limit = 5

(* ---- 位置 ---- *)

type location =
  | Reg of string       (* 分配了物理寄存器 *)
  | Stack of int         (* 溢出到栈，offset 相对 sp *)

(* ---- 每函数分配结果 ---- *)

type func_alloc = {
  vreg_loc      : location IntMap.t;    (* vreg → Reg 或 Stack offset *)
  allocas       : int IntMap.t;         (* alloca vreg → sp offset *)
  saved_regs    : (string * int) list;  (* 需在序言/尾声保存恢复的 callee-saved *)
  frame_size    : int;                  (* 总栈帧大小 (16 对齐) *)
  save_ra       : bool;                 (* 本函数是否需要保存 ra *)
  ra_offset     : int;                  (* ra 保存偏移 *)
  outgoing_size : int;                  (* 超出 8 个寄存器参数的调用溢出区大小 *)
}

type alloc_result = func_alloc StringMap.t

(* ---- 辅助 ---- *)

let align_to n align =
  if n mod align = 0 then n else n + (align - (n mod align))

let collect_allocas f =
  List.fold_left
    (fun acc (_, bb) ->
       List.fold_left
         (fun acc instr ->
            match instr with
            | Alloca { dst; _ } -> IntSet.add dst acc
            | _ -> acc)
         acc bb.bb_instrs)
    IntSet.empty f.f_blocks

let max_outgoing_stack_args f =
  List.fold_left
    (fun max_args (_, bb) ->
       List.fold_left
         (fun max_args instr ->
            match instr with
            | Call { args; _ } -> max max_args (max 0 (List.length args - 8))
            | _ -> max_args)
         max_args bb.bb_instrs)
    0 f.f_blocks

let has_calls f =
  List.exists
    (fun (_, bb) ->
       List.exists
         (function
           | Call _ -> true
           | _ -> false)
         bb.bb_instrs)
    f.f_blocks

(* ---- 线性扫描 ---- *)

(* 对单个函数做寄存器分配，返回 func_alloc *)
let allocate_func (f : func) (intervals : Live_intervals.interval list) =
    let save_ra = has_calls f in
    let allocatable_regs = if save_ra then nonleaf_regs else leaf_regs in
    let num_regs = Array.length allocatable_regs in
    (* 参数 vreg 集合：leaf 函数里它们只允许落到前 leaf_param_limit 个寄存器（t0-t4） *)
    let param_set =
      List.fold_left (fun s (_, r) -> IntSet.add r s) IntSet.empty f.f_params
    in
    let param_limit = if save_ra then num_regs else leaf_param_limit in
  let alloca_set = collect_allocas f in
  (* 过滤掉 alloca vreg，它们不参与寄存器分配 *)
  let intervals =
    List.filter (fun (i : Live_intervals.interval) -> not (IntSet.mem i.vreg alloca_set)) intervals
  in
  (* 按 start 排序 *)
  let intervals = List.sort (fun a b -> compare a.start b.start) intervals in

  (* active 列表: (vreg, stop, register_index) *)
  let active : (int * int * int) list ref = ref [] in
  (* vreg → location（Reg 的暂不填 offset，Spilled 的先记一个占位） *)
  let vreg_map : (int, location) Hashtbl.t =
    Hashtbl.create (List.length intervals)
  in
  (* 可用寄存器索引池 *)
  let free_regs : int list ref = ref (List.init num_regs (fun i -> i)) in

  (* 淘汰 stop < pos 的活跃区间，释放其寄存器 *)
  let expire_old_intervals pos =
    let stay, gone = List.partition (fun (_, stop, _) -> stop >= pos) !active in
    gone |> List.iter (fun (_, _, ri) -> free_regs := ri :: !free_regs);
    active := stay
  in

  (* 从 active 中找到 stop 最远的那个区间 *)
  let farthest_active () =
    match !active with
    | [] -> None
    | h :: t ->
      Some (List.fold_left
        (fun best item ->
           let (_, s1, _) = best in
           let (_, s2, _) = item in
           if s2 > s1 then item else best)
        h t)
  in

  List.iter (fun { Live_intervals.vreg; start; stop } ->
    expire_old_intervals start;
    if IntSet.mem vreg param_set then begin
      (* 参数 vreg：只允许前 param_limit 个寄存器（leaf 时即 t0-t4），
         避免与 a0-a7 参数传入寄存器发生拷贝顺序冲突 *)
      match List.find_opt (fun i -> i < param_limit) !free_regs with
      | Some ri ->
        free_regs := List.filter (fun i -> i <> ri) !free_regs;
        Hashtbl.replace vreg_map vreg (Reg allocatable_regs.(ri));
        active := (vreg, stop, ri) :: !active
      | None ->
        Hashtbl.replace vreg_map vreg (Stack (-1))
      end
    else
      match !free_regs with
      | [] ->
        (* 寄存器不够，需要溢出 *)
        begin match farthest_active () with
        | Some (spill_vreg, far_stop, ri) when far_stop > stop ->
          (* 溢出 stop 最远的活跃 vreg，把寄存器给当前 vreg *)
          Hashtbl.replace vreg_map spill_vreg (Stack (-1));
          active := List.filter (fun (v, _, _) -> v <> spill_vreg) !active;
          Hashtbl.replace vreg_map vreg (Reg allocatable_regs.(ri));
          active := (vreg, stop, ri) :: !active
        | _ ->
          (* 当前 vreg 的 stop 更远，直接溢出当前 vreg *)
          Hashtbl.replace vreg_map vreg (Stack (-1))
        end
      | ri :: rest ->
        free_regs := rest;
        Hashtbl.replace vreg_map vreg (Reg allocatable_regs.(ri));
        active := (vreg, stop, ri) :: !active
  ) intervals;

  (* ---- 构建栈帧 ---- *)

  let outgoing_size = 4 * max_outgoing_stack_args f in
  let next_offset = ref outgoing_size in

  (* 给溢出的 vreg 分配栈偏移 *)
  Hashtbl.iter (fun v loc ->
    match loc with
    | Stack _ ->
      Hashtbl.replace vreg_map v (Stack !next_offset);
      next_offset := !next_offset + 4
    | Reg _ -> ()
  ) vreg_map;

  (* alloca vreg 的栈偏移 *)
  let alloca_offsets = ref IntMap.empty in
  IntSet.iter (fun v ->
    alloca_offsets := IntMap.add v !next_offset !alloca_offsets;
    next_offset := !next_offset + 4
  ) alloca_set;

    let used_saved_regs =
      Hashtbl.fold (fun _ loc acc ->
        match loc with
        | Reg reg when String.length reg > 0 && reg.[0] = 's' ->
          if List.mem reg acc then acc else reg :: acc
        | _ -> acc)
        vreg_map []
      |> List.sort String.compare
    in
    let saved_regs =
      List.map (fun reg ->
        let offset = !next_offset in
        next_offset := !next_offset + 4;
        (reg, offset)
      ) used_saved_regs
    in

    let raw_size = !next_offset + if save_ra then 4 else 0 in
  let frame_size = align_to raw_size 16 in
    let ra_offset = if save_ra then frame_size - 4 else -1 in

  (* 导出 vreg_loc *)
  let vreg_loc = ref IntMap.empty in
  Hashtbl.iter (fun v loc -> vreg_loc := IntMap.add v loc !vreg_loc) vreg_map;

      { vreg_loc = !vreg_loc; allocas = !alloca_offsets; saved_regs;
        frame_size; save_ra; ra_offset; outgoing_size }

(* ---- 入口 ---- *)

let allocate (m : module_) (intervals_list : (string * Live_intervals.interval list) list)
    : module_ * alloc_result =
  let interval_map =
    List.fold_left (fun acc (name, ivs) -> StringMap.add name ivs acc)
      StringMap.empty intervals_list
  in
  let result = ref StringMap.empty in
  List.iter (fun (name, f) ->
    let ivs = try StringMap.find name interval_map with Not_found -> [] in
    let fa = allocate_func f ivs in
    result := StringMap.add name fa !result
  ) m.m_funcs;
  m, !result
