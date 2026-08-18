(* ToyC 优化 — 循环旋转实现细节

   流水线不再直接把这一步作为 “LoopRotate pass” ，
   而是通过 Loop_canonicalize.run 统一调用。这里保留的是当前
   规范化 pass 里使用到的 rotate-based 变换实现。

   把 while 形式的循环改写成 do-while 形式：

   旋转前：
     preheader: jmp header
     header:    phi ...; cond = icmp ...; br cond, latch, exit
     latch:     body; jmp header

   旋转后：
     preheader: cond_init = clone(cond, phi <- preheader incoming); br cond_init, latch, exit
     latch:     phi ...; (header 原纯指令) body; cond_next = clone(cond, phi <- latch incoming);
                br cond_next, latch, exit

   该变换把入口条件判断放到 preheader，把每轮条件判断下沉到 latch。 *)

open Ir_types
open Loop_info

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

(* 把 f.f_blocks 列表转换为 label -> basic_block 的映射。 *)
let build_bmap (f : func) : basic_block IntMap.t =
  List.fold_left (fun m (lbl, bb) -> IntMap.add lbl bb m) IntMap.empty f.f_blocks

(* 返回终结指令的所有后继标号。 *)
let term_succs (t : terminator) : label list =
  match t with
  | Jump l -> [ l ]
  | Br (_, t, f) -> [ t; f ]
  | Ret _ -> []

(* 在 phi incoming 列表中查找指定前驱对应的值。 *)
let find_incoming (lbl : label) (incoming : (value * label) list) : value option =
  Option.map fst (List.find_opt (fun (_, pred) -> pred = lbl) incoming)

(* 根据 env 替换 vreg；env 中不存在的 vreg 保持不变。 *)
let map_value (env : value IntMap.t) (v : value) : value =
  match v with
  | Imm _ | Global _ -> v
  | VReg r -> (match IntMap.find_opt r env with Some v -> v | None -> v)

(* 仅允许在 header 中复制这些纯指令；遇到内存/调用/phi 等直接放弃本轮旋转。 *)
let is_pure_non_phi (i : instr) : bool =
  match i with
  | Binop _ | Icmp _ | Shl _ | AShr _ | And _ | Zext _ | Copy _ -> true
  | Alloca _ | Load _ | Store _ | Call _ | Phi _ -> false

(* 分离基本块头部连续的 phi 指令与其余指令。 *)
let partition_header_instrs (bb : basic_block) : instr list * instr list =
  let rec take_phis acc = function
    | Phi _ as i :: tl -> take_phis (i :: acc) tl
    | rest -> (List.rev acc, rest)
  in
  take_phis [] bb.bb_instrs

(* 复制一条纯指令，给 dst 分配新 vreg，并对 operands 应用 remap。 *)
let clone_pure (fresh : unit -> int) (remap : value -> value) (i : instr)
    : instr * int * int =
  match i with
  | Binop { dst; op; lhs; rhs } ->
      let dst' = fresh () in
      (Binop { dst = dst'; op; lhs = remap lhs; rhs = remap rhs }, dst, dst')
  | Icmp { dst; cond; lhs; rhs } ->
      let dst' = fresh () in
      (Icmp { dst = dst'; cond; lhs = remap lhs; rhs = remap rhs }, dst, dst')
  | Shl { dst; lhs; rhs } ->
      let dst' = fresh () in
      (Shl { dst = dst'; lhs = remap lhs; rhs = remap rhs }, dst, dst')
  | AShr { dst; lhs; rhs } ->
      let dst' = fresh () in
      (AShr { dst = dst'; lhs = remap lhs; rhs = remap rhs }, dst, dst')
  | And { dst; lhs; rhs } ->
      let dst' = fresh () in
      (And { dst = dst'; lhs = remap lhs; rhs = remap rhs }, dst, dst')
  | Zext { dst; src } ->
      let dst' = fresh () in
      (Zext { dst = dst'; src = remap src }, dst, dst')
  | Copy { dst; src } ->
      let dst' = fresh () in
      (Copy { dst = dst'; src = remap src }, dst, dst')
  | _ -> raise Exit

(* 复制一串 header 纯指令。env 负责把 phi dst 映射到某条入边的值，
   同时逐条记录旧 dst -> 新 dst，供后续指令引用。 *)
(* 复制一串纯指令，并维护旧 dst 到新 dst 的映射。 *)
let clone_chain (fresh : unit -> int) (init_env : value IntMap.t) (instrs : instr list)
    : instr list * value IntMap.t =
  let env = ref init_env in
  let cloned =
    List.map (fun instr ->
      let (instr', old_dst, new_dst) = clone_pure fresh (map_value !env) instr in
      env := IntMap.add old_dst (VReg new_dst) !env;
      instr'
    ) instrs
  in
  (cloned, !env)

(* 根据 header phi 的指定前驱入边，构造 dst -> incoming value 的映射。 *)
let build_phi_env (header_phis : instr list) (pred : label) : value IntMap.t =
  List.fold_left (fun m instr ->
    match instr with
    | Phi { dst; incoming } ->
        (match find_incoming pred incoming with
         | Some v -> IntMap.add dst v m
         | None -> raise Exit)
    | _ -> m
  ) IntMap.empty header_phis

(* 在循环旋转后修复 loop 外对旧 header 定义值的使用。
   参考 LLVM 的 SSAUpdater 思路：
   1. 在 exit block 上为需要外流的 header 值建立出口 phi；
   2. 把被 exit block 支配到的 loop 外 uses 统一改写到这些出口 phi。 *)
let rewrite_exit_uses (f : func) (bmap : basic_block IntMap.t)
    (loop_blocks : IntSet.t) (header_defined : IntSet.t)
    (header : label) (exit_target : label) (preheader : label) (latch : label)
    (pre_env_final : value IntMap.t) (latch_env_final : value IntMap.t)
    (fresh_vreg : unit -> int)
    : basic_block IntMap.t =
  let exit_bb = IntMap.find exit_target bmap in
  let exit_succs = term_succs exit_bb.bb_term in
  let inserted = ref IntMap.empty in
  let bmap =
    IntMap.map (fun bb ->
      if bb.bb_label <> exit_target then bb
      else
        let updated_existing_phis =
          List.map (function
            | Phi { dst; incoming } ->
                let expanded =
                  List.concat_map (fun (v, l) ->
                    if l = header then
                        [ (map_value latch_env_final v, latch);
                        (map_value pre_env_final v, preheader) ]
                    else
                      [ (v, l) ]
                  ) incoming
                in
                let seen = ref IntSet.empty in
                let incoming' =
                  List.filter (fun (_, l) ->
                    if IntSet.mem l !seen then false
                    else (seen := IntSet.add l !seen; true)
                  ) expanded
                in
                Phi { dst; incoming = incoming' }
            | i -> i
          ) bb.bb_instrs
        in
          let needed = header_defined in
        let missing =
          IntSet.filter (fun r ->
            not (List.exists (function
              | Phi { dst; _ } -> dst = r
              | _ -> false) updated_existing_phis))
            needed
        in
        IntSet.fold (fun r acc ->
          let r' = fresh_vreg () in
          inserted := IntMap.add r r' !inserted;
          let incoming =
            [ (map_value pre_env_final (VReg r), preheader);
                (map_value latch_env_final (VReg r), latch) ]
          in
          let phi = Phi { dst = r'; incoming } in
          let replace_instr = function
            | Phi _ as i -> i
            | i -> Loop_unroll.map_instr_values (fun x ->
                if x = r then Some (VReg r') else None) i
          in
          let instrs = phi :: List.map replace_instr acc.bb_instrs in
          let term =
            Loop_unroll.map_term_values (fun x ->
              if x = r then Some (VReg r') else None) acc.bb_term
          in
          { acc with bb_instrs = instrs; bb_term = term })
        missing { bb with bb_instrs = updated_existing_phis }
    ) bmap
  in
  let bmap =
    IntMap.mapi (fun lbl bb ->
    if List.mem lbl exit_succs then
      let instrs = List.map (function
        | Phi p ->
            let incoming =
              List.map (fun (v, pred) ->
                if pred = exit_target then
                  match v with
                  | VReg r when IntMap.mem r !inserted ->
                      (VReg (IntMap.find r !inserted), pred)
                  | _ -> (v, pred)
                else (v, pred))
                p.incoming
            in
            Phi { p with incoming }
        | i -> i) bb.bb_instrs in
      { bb with bb_instrs = instrs }
      else bb) bmap
  in
  let replace_vreg r =
    match IntMap.find_opt r !inserted with
    | Some r' -> Some (VReg r')
    | None -> None
  in
  let map_replaced_value v =
    match v with
    | Imm _ | Global _ -> v
    | VReg r -> Option.value ~default:v (replace_vreg r)
  in
  let temp_func =
    { f with
      f_blocks =
        IntMap.bindings bmap |> List.sort (fun (a, _) (b, _) -> compare a b) }
  in
  let dom = Dominance.analyze temp_func in
  IntMap.mapi (fun lbl bb ->
    let dominated_by_exit =
      match IntMap.find_opt lbl dom.doms with
      | Some ds -> IntSet.mem exit_target ds
      | None -> false
    in
    if lbl = exit_target || IntSet.mem lbl loop_blocks || not dominated_by_exit then
      bb
    else
      let instrs =
        List.map (function
          | Phi p ->
              let incoming =
                List.map (fun (v, pred) -> (map_replaced_value v, pred)) p.incoming
              in
              Phi { p with incoming }
          | i -> Loop_unroll.map_instr_values replace_vreg i) bb.bb_instrs
      in
      let term = Loop_unroll.map_term_values replace_vreg bb.bb_term in
      { bb with bb_instrs = instrs; bb_term = term }) bmap

(* 对满足条件的循环执行一次 do-while 旋转；失败返回 None。 *)
let rotate_loop (f : func) (bmap : basic_block IntMap.t) (lp : loop)
    : (basic_block IntMap.t * int) option =
  let header = lp.header in
  if header = f.f_entry then None
  else
    match lp.preheader, lp.latches with
    | Some preheader, [ latch ] when header <> latch ->
        let hb = IntMap.find header bmap in
        let lb = IntMap.find latch bmap in
        let pb = IntMap.find preheader bmap in
        begin match hb.bb_term with
        | Br (cond, t_lbl, f_lbl) ->
            let targets =
              if t_lbl = latch && not (IntSet.mem f_lbl lp.blocks) then Some (t_lbl, f_lbl)
              else if f_lbl = latch && not (IntSet.mem t_lbl lp.blocks) then Some (f_lbl, t_lbl)
              else None
            in
            begin match targets with
            | None -> None
            | Some (loop_target, exit_target) ->
                if loop_target <> latch
                   || exit_target = preheader
                   || exit_target = header
                   || exit_target = latch
                then None
                else
                  begin match pb.bb_term with
                  | Jump target when target = header ->
                      let header_phis, header_rest = partition_header_instrs hb in
                      if List.exists (fun i -> not (is_pure_non_phi i)) header_rest then None
                      else if List.exists (function Phi _ -> true | _ -> false) lb.bb_instrs then None
                      else if lb.bb_term <> Jump header then None
                      else if IntMap.exists (fun lbl bb ->
                        lbl <> preheader && lbl <> latch
                        && List.mem header (term_succs bb.bb_term)) bmap
                      then None
                      else begin
                        try
                          let next_vreg = ref (f.f_max_vreg + 1) in
                          let fresh_vreg () = let x = !next_vreg in incr next_vreg; x in

                          let pre_env = build_phi_env header_phis preheader in
                          let latch_env = build_phi_env header_phis latch in
                          let pre_clone, pre_env_final =
                            clone_chain fresh_vreg pre_env header_rest in
                          let latch_clone, latch_env_final =
                            clone_chain fresh_vreg latch_env header_rest in

                          let guard_cond = map_value pre_env_final cond in
                          let bottom_cond = map_value latch_env_final cond in

                          let new_latch =
                            { bb_label = latch;
                              bb_instrs =
                                header_phis @ header_rest @ lb.bb_instrs @ latch_clone;
                              bb_term = Br (bottom_cond, t_lbl, f_lbl) }
                          in
                          let new_preheader =
                            { pb with
                              bb_instrs = pb.bb_instrs @ pre_clone;
                              bb_term = Br (guard_cond, t_lbl, f_lbl) }
                          in

                          let bmap = IntMap.remove header bmap in
                          let bmap = IntMap.add preheader new_preheader bmap in
                          let bmap = IntMap.add latch new_latch bmap in

                          let header_defined =
                            List.fold_left (fun s instr ->
                              match instr_dst instr with
                              | Some d -> IntSet.add d s
                              | None -> s)
                              IntSet.empty (header_phis @ header_rest)
                          in
                          let bmap =
                              rewrite_exit_uses f bmap lp.blocks header_defined
                                header exit_target preheader latch
                                pre_env_final latch_env_final fresh_vreg
                          in
                          Some (bmap, !next_vreg - 1)
                        with Exit -> None
                      end
                  | _ -> None
                  end
            end
        | _ -> None
        end
    | _ -> None

(* 对单个函数反复旋转循环直到无可旋转。 *)
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
    match List.find_map (rotate_loop f bmap) loops with
    | None -> f
    | Some (bmap', new_max_vreg) ->
        fixpoint
          { f with
            f_blocks =
              IntMap.bindings bmap'
              |> List.sort (fun (a, _) (b, _) -> compare a b);
            f_max_vreg = new_max_vreg }
  in
  fixpoint f

(* 模块入口：逐函数运行循环旋转。 *)
let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
