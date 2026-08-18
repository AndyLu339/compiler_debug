(* Phi 并行拷贝调度 — 用拓扑排序避免不必要的栈临时槽

   Phi 指令的并行语义要求：所有 src 的读取必须先于任何 dst 的写入。
   即使 Phi 之间互相引用（如 swap: %1←%2 且 %2←%1），也必须正确。

   本模块将拷贝列表规划为一组 action，只在真循环时才使用栈临时槽。
   无环情况（绝大多数 Phi）直接按拓扑序发射，零栈开销。 *)

open Ir_types

module IntMap = Map.Make (Int)

(* 规划结果：codegen 按顺序执行每个 action *)
type phi_action =
  | Direct of (int * value)        (* dst ← src，直接拷贝，无临时槽 *)
  | SaveTemp of (value * int)      (* 将 src 值保存到临时槽 idx，
                                      必须先于所有写入该 src 的 copy *)
  | LoadTemp of (int * int)        (* 从临时槽 idx 加载到 dst *)

let schedule (copies : (int * value) list) : phi_action list =
  let n = List.length copies in
  if n = 0 then []
  else
    (* 构建 def_map：vreg → 定义它的 copy 索引 *)
    let def_map =
      List.fold_left
        (fun m (i, (dst, _)) -> IntMap.add dst i m)
        IntMap.empty
        (List.mapi (fun i c -> (i, c)) copies)
    in

    (* 构建依赖图：边 A → B 表示 A 必须在 B 之前执行
       规则：若 A 的 src 是 VReg r，且 r 被 B 定义（dst_B = r），
             则 A 读取 r 必须先于 B 写入 r，即 A → B *)
    let edges = Array.make n [] in
    let in_degree = Array.make n 0 in
    List.iteri (fun i (_, src) ->
      match src with
      | VReg r ->
        begin match IntMap.find_opt r def_map with
        | Some j when j <> i ->
          edges.(i) <- j :: edges.(i);
          in_degree.(j) <- in_degree.(j) + 1
        | _ -> ()
        end
      | Imm _ | Global _ -> ()
    ) copies;

    let remaining = Array.make n true in
    let broken = Array.make n (-1) in  (* -1 表示未破坏，≥0 表示临时槽编号 *)
    let pre_saves = ref [] in
    let body = ref [] in
    let temp_counter = ref 0 in

    let find_ready () =
      let rec loop i =
        if i >= n then None
        else if remaining.(i) && in_degree.(i) = 0 then Some i
        else loop (i + 1)
      in loop 0
    in

    let has_remaining () =
      let rec loop i =
        if i >= n then false
        else if remaining.(i) then true
        else loop (i + 1)
      in loop 0
    in

    let first_remaining () =
      let rec loop i =
        if remaining.(i) then i else loop (i + 1)
      in loop 0
    in

    let rec process () =
      match find_ready () with
      | Some i ->
        let (dst, src) = List.nth copies i in
        if broken.(i) >= 0 then
          body := LoadTemp (dst, broken.(i)) :: !body
        else
          body := Direct (dst, src) :: !body;
        remaining.(i) <- false;
        List.iter (fun j ->
          if remaining.(j) then
            in_degree.(j) <- in_degree.(j) - 1
        ) edges.(i);
        process ()
      | None ->
        if has_remaining () then (
          (* 死锁 = 有环：选一个 copy，把它的 src 保存到临时槽来破环 *)
          let i = first_remaining () in
          let (_, src) = List.nth copies i in
          let tidx = !temp_counter in
          incr temp_counter;
          pre_saves := SaveTemp (src, tidx) :: !pre_saves;
          broken.(i) <- tidx;
          (* 移除出边：src 已保存，不再阻塞写入方 *)
          List.iter (fun j ->
            if remaining.(j) then
              in_degree.(j) <- in_degree.(j) - 1
          ) edges.(i);
          edges.(i) <- [];
          process ()
        )
    in

    process ();
    (* pre_saves 必须最先执行（保存旧值），
       然后按拓扑序执行 Direct/LoadTemp *)
    List.rev_append !pre_saves (List.rev !body)
