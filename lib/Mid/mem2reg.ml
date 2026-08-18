(* ToyC mem2reg — 内存模型 → SSA 提升
   算法: 经典的 Cyctron et al. SSA 构造
   1. 收集 alloca → 找每个 alloca 有 store 的块
   2. 迭代支配边界 → 插入空 φ 节点
   3. DFS 重命名 (沿支配树) → 维护值栈, 替换 load/store
   4. (已合并到第三遍) *)

open Ir_types

module IntSet = Set.Make(Int)
module IntMap = Map.Make(Int)

(* ====================================================================== *)
(* 工具函数                                                               *)
(* ====================================================================== *)

(* 块列表 → label map *)
let block_map_of_list (blks : (label * basic_block) list) : basic_block IntMap.t =
  List.fold_left (fun m (lbl, bb) -> IntMap.add lbl bb m) IntMap.empty blks

(* label map → 块列表 (保持原顺序) *)
let block_list_of_map (labels : label list) (m : basic_block IntMap.t) : (label * basic_block) list =
  List.map (fun lbl -> (lbl, IntMap.find lbl m)) labels

(* 后继 *)
let compute_succs (f : func) : IntSet.t IntMap.t =
  List.fold_left (fun acc (lbl, bb) ->
    let succs = match bb.bb_term with
      | Jump l       -> [ l ]
      | Br (_, t, f) -> [ t; f ]
      | Ret _        -> []
    in
    IntMap.add lbl (IntSet.of_list succs) acc
  ) IntMap.empty f.f_blocks

(* 前驱 *)
let compute_preds (succs : IntSet.t IntMap.t) : IntSet.t IntMap.t =
  IntMap.fold (fun lbl targets acc ->
    IntSet.fold (fun t acc ->
      IntMap.update t (fun prev ->
        Some (IntSet.add lbl (Option.value prev ~default:IntSet.empty))
      ) acc
    ) targets acc
  ) succs IntMap.empty

(* 在 value 中递归应用替换 *)
let rec apply_repl_value (repl : value IntMap.t) (v : value) : value =
  match v with
  | VReg r ->
    (match IntMap.find_opt r repl with
     | Some v' -> apply_repl_value repl v'
     | None -> v)
  | Imm _ | Global _ -> v

(* 在指令中应用所有替换 (只替换 operands, 不替换 dst) *)
let apply_repl_instr (repl : value IntMap.t) (i : instr) : instr =
  let r v = apply_repl_value repl v in
  match i with
  | Alloca _ -> i
  | Load l   -> Load { l with ptr = r l.ptr }
  | Store s  -> Store { val_ = r s.val_; ptr = r s.ptr }
  | Binop b  -> Binop { b with lhs = r b.lhs; rhs = r b.rhs }
  | Icmp c   -> Icmp { c with lhs = r c.lhs; rhs = r c.rhs }
  | Call c   -> Call { c with args = List.map r c.args }
  | Phi p    -> Phi { p with incoming = List.map (fun (v, lbl) -> (r v, lbl)) p.incoming }
  | Shl s    -> Shl { s with lhs = r s.lhs; rhs = r s.rhs }
  | AShr s   -> AShr { s with lhs = r s.lhs; rhs = r s.rhs }
  | And a    -> And { a with lhs = r a.lhs; rhs = r a.rhs }
  | Zext z   -> Zext { z with src = r z.src }
  | Copy c   -> Copy { c with src = r c.src }

(* 在终结指令中应用所有替换 *)
let apply_repl_term (repl : value IntMap.t) (t : terminator) : terminator =
  let r v = apply_repl_value repl v in
  match t with
  | Ret (Some v) -> Ret (Some (r v))
  | Ret None     -> Ret None
  | Br (cond, t_lbl, f_lbl) -> Br (r cond, t_lbl, f_lbl)
  | Jump _ -> t

(* 对整个块应用替换 *)
let apply_repl_block (repl : value IntMap.t) (bb : basic_block) : basic_block =
  { bb with
    bb_instrs = List.map (apply_repl_instr repl) bb.bb_instrs;
    bb_term   = apply_repl_term repl bb.bb_term;
  }

(* 对整个函数的所有块应用替换 *)
let apply_repl_func (repl : value IntMap.t) (block_map : basic_block IntMap.t)
    : basic_block IntMap.t =
  IntMap.map (apply_repl_block repl) block_map

(* ====================================================================== *)
(* 第一遍: 收集 alloca 和 store 块                                       *)
(* ====================================================================== *)

(* 找出函数中所有的 alloca vreg *)
let find_allocas (block_map : basic_block IntMap.t) : IntSet.t =
  IntMap.fold (fun _ bb acc ->
    List.fold_left (fun acc i ->
      match i with Alloca { dst; _ } -> IntSet.add dst acc | _ -> acc
    ) acc bb.bb_instrs
  ) block_map IntSet.empty

(* 对每个 alloca, 记录哪些块有 store *)
let find_store_blocks (block_map : basic_block IntMap.t) (allocas : IntSet.t)
    : IntSet.t IntMap.t =
  IntMap.fold (fun lbl bb acc ->
    List.fold_left (fun acc i ->
      match i with
      | Store { ptr = VReg ptr; _ } when IntSet.mem ptr allocas ->
        IntMap.update ptr (fun s ->
          Some (IntSet.add lbl (Option.value s ~default:IntSet.empty))
        ) acc
      | _ -> acc
    ) acc bb.bb_instrs
  ) block_map IntMap.empty

(* ====================================================================== *)
(* 第二遍: 迭代支配边界 → 插入 φ 节点                                    *)
(* ====================================================================== *)

(* 对单个 alloca: 按 Cytron 的 iterated dominance frontier 放置 φ。
   关键点是：即便某个块本身也有 store，只要它位于别的定义块的支配边界上，
   且在块头需要合流来自不同前驱的值，仍然必须插 φ。
   例如:
     bb0: store a
     if (...) bb1: store a
     bb2: load a; store a
   这里 bb2 也是定义块，但块头的 load 仍然需要 φ。*)
let compute_phi_blocks (def_blocks : IntSet.t) (dom_front : IntSet.t IntMap.t) : IntSet.t =
  let has_phi = ref IntSet.empty in
  let queued = ref def_blocks in
  let worklist = ref (IntSet.elements def_blocks) in
  while !worklist <> [] do
    let blk = List.hd !worklist in
    worklist := List.tl !worklist;
    let df = Option.value (IntMap.find_opt blk dom_front) ~default:IntSet.empty in
    IntSet.iter (fun frontier_blk ->
      if not (IntSet.mem frontier_blk !has_phi) then begin
        has_phi := IntSet.add frontier_blk !has_phi;
        if not (IntSet.mem frontier_blk !queued) then begin
          queued := IntSet.add frontier_blk !queued;
          worklist := frontier_blk :: !worklist
        end
      end
    ) df
  done;
  !has_phi

(* 给一个 alloca 在指定块插入 φ 节点 *)
let insert_phis_for_alloca
    (block_map : basic_block IntMap.t)
    (phi_blocks : IntSet.t)
    (alloca : int)
    (next_vreg : int ref)
    (phi_map : int IntMap.t ref)  (* phi_vreg → alloca *)
    : basic_block IntMap.t =
  IntSet.fold (fun lbl block_map ->
    let bb = IntMap.find lbl block_map in
    let dst = !next_vreg in
    incr next_vreg;
    phi_map := IntMap.add dst alloca !phi_map;
    let phi = Phi { dst; incoming = [] } in
    IntMap.add lbl { bb with bb_instrs = phi :: bb.bb_instrs } block_map
  ) phi_blocks block_map

(* ====================================================================== *)
(* 第三遍: DFS 重命名 (沿支配树)                                          *)
(* ====================================================================== *)

let rename_func
    (block_map : basic_block IntMap.t)
    (entry : label)
    (succs : IntSet.t IntMap.t)
    (dom_children : IntSet.t IntMap.t)
    (allocas : IntSet.t)
    (phi_map : int IntMap.t)    (* phi_vreg → alloca *)
    : basic_block IntMap.t * value IntMap.t =
  (* 每个 alloca 一个值栈 *)
  let stacks : value list IntMap.t ref = ref IntMap.empty in
  (* load_dst → 替换值 *)
  let load_repl : value IntMap.t ref = ref IntMap.empty in
  let block_map = ref block_map in

  let stack_top alloca =
    match IntMap.find_opt alloca !stacks with
    | Some (top :: _) -> top
    | Some [] | None ->
      (* undef: 循环体内声明的局部变量，其 alloca 在从循环入口到 header 的
         路径上没有 store。这里用 VReg (-1) 作为占位哨兵，表示"未定义值"。
         哨兵值不会被任何指令实际读取 — 循环体总会先 store 再 load。
         用 VReg (-1) 而非 Imm 0，避免和真正的常量 0 混淆。 *)
      VReg (-1)
  in

  let push alloca v =
    stacks := IntMap.update alloca (function
      | None   -> Some [ v ]
      | Some vs -> Some (v :: vs)
    ) !stacks
  in

  let pop_n alloca n =
    stacks := IntMap.update alloca (function
      | Some vs ->
        let rec drop k xs = if k <= 0 then xs else
          match xs with _ :: rest -> drop (k - 1) rest | [] -> []
        in
        let rest = drop n vs in
        if rest = [] then None else Some rest
      | None -> None
    ) !stacks
  in

  let rec dfs (blk : label) =
    let bb = IntMap.find blk !block_map in
    (* 本块压入栈的计数 (per alloca) *)
    let pushed : int IntMap.t ref = ref IntMap.empty in

    let inc_pushed alloca =
      pushed := IntMap.update alloca (function
        | None -> Some 1 | Some n -> Some (n + 1)) !pushed
    in

    (* 处理每条指令 *)
    let new_instrs = List.filter_map (fun instr ->
      match instr with
      (* φ 节点: 定义新值 → 压入对应的 alloca 栈 *)
      | Phi { dst; _ } when IntMap.mem dst phi_map ->
        let alloca = IntMap.find dst phi_map in
        push alloca (VReg dst);
        inc_pushed alloca;
        Some instr

      (* load from alloca: 用栈顶替换, 删除 *)
      | Load { dst; ptr = VReg ptr } when IntSet.mem ptr allocas ->
        let top = stack_top ptr in
        load_repl := IntMap.add dst top !load_repl;
        None

      (* store to alloca: 压栈, 删除
         Note: 这里只 push 不 pop——看上去旧栈底值永远不再被读到，好像该先 pop 再 push（覆盖语义）。
         但不先 pop 是因为出块时统一调用 pop_n 恢复栈状态，push-only 实现更简单，无需在每次 store
         时额外判断栈是否已有值。 *)
      | Store { val_; ptr = VReg ptr } when IntSet.mem ptr allocas ->
        (* 先把 load 替换应用到 val_ *)
        let val_ = apply_repl_value !load_repl val_ in
        push ptr val_;
        inc_pushed ptr;
        None

      (* 原 alloca 指令: 已完成使命，删除 *)
      | Alloca { dst; _ } when IntSet.mem dst allocas ->
        None

      | _ ->
        (* 普通指令: 应用 load 替换 *)
        Some (apply_repl_instr !load_repl instr)
    ) bb.bb_instrs in

    (* 更新终结指令 *)
    let new_term = apply_repl_term !load_repl bb.bb_term in

    block_map := IntMap.add blk
      { bb with bb_instrs = new_instrs; bb_term = new_term }
      !block_map;

    (* 给后继块的 φ 节点填本块的入边 *)
    (match IntMap.find_opt blk succs with
     | Some succ_set ->
       IntSet.iter (fun succ ->
         let succ_bb = IntMap.find succ !block_map in
         let succ_instrs = List.map (fun instr ->
           match instr with
           | Phi p when IntMap.mem p.dst phi_map ->
             let alloca = IntMap.find p.dst phi_map in
             let val_ = stack_top alloca in
             Phi { p with incoming = (val_, blk) :: p.incoming }
           | _ -> instr
         ) succ_bb.bb_instrs in
         block_map := IntMap.add succ
           { succ_bb with bb_instrs = succ_instrs }
           !block_map
       ) succ_set
     | None -> ());

    (* 递归子节点 *)
    (match IntMap.find_opt blk dom_children with
     | Some children -> IntSet.iter dfs children
     | None -> ());

    (* 出块: 弹出本块压入的值 *)
    IntMap.iter (fun alloca n -> pop_n alloca n) !pushed
  in

  dfs entry;

  (* 将 load 替换应用到所有块 (处理跨块引用) *)
  block_map := apply_repl_func !load_repl !block_map;

  !block_map, !load_repl

(* ====================================================================== *)
(* 每个函数的主流程                                                       *)
(* ====================================================================== *)

let promote_func (f : func) : func =
  let labels = List.map fst f.f_blocks in
  let block_map = block_map_of_list f.f_blocks in
  let allocas = find_allocas block_map in

  if IntSet.is_empty allocas then f
  else begin
    let succs = compute_succs f in
    let dom_info = Dominance.analyze f in
    let alloca_defs = find_store_blocks block_map allocas in

    (* 记录哪些 alloca 实际上被 store 过 (没被 store 过的跳过) *)
    let promoted = IntMap.fold (fun alloca def_blks acc ->
      if IntSet.is_empty def_blks then acc
      else IntSet.add alloca acc
    ) alloca_defs IntSet.empty in

    if IntSet.is_empty promoted then f
    else begin
      let next_vreg = ref (f.f_max_vreg + 1) in
      let phi_map : int IntMap.t ref = ref IntMap.empty in

      (* 阶段 1: 为每个 promoted alloca 插 φ *)
      let block_map =
        IntMap.fold (fun alloca def_blks block_map ->
          let phi_blks = compute_phi_blocks def_blks dom_info.Dominance.dom_front in
          if IntSet.is_empty phi_blks then block_map
          else insert_phis_for_alloca block_map phi_blks alloca next_vreg phi_map
        ) alloca_defs block_map
      in

      (* 阶段 2: 重命名 (含 alloca 删除) *)
      let block_map, _load_repl =
        rename_func block_map f.f_entry succs
          dom_info.Dominance.children promoted !phi_map
      in

      { f with f_blocks = block_list_of_map labels block_map;
               f_max_vreg = !next_vreg - 1 }
    end
  end

(* ====================================================================== *)
(* 模块入口                                                               *)
(* ====================================================================== *)

let promote (m : module_) : module_ =
  { m with m_funcs = List.map (fun (name, f) -> (name, promote_func f)) m.m_funcs }
