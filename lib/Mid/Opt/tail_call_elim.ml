(* ToyC 优化 — 尾递归消除
   将自递归尾调用转为循环: Call(f, args) + Ret(v) → args赋值 + Jump entry
   通过 phi 节点在 SSA 中传递新参数值 *)

open Ir_types

module IntMap = Map.Make (Int)

(* ---- tail call 识别 ---------------------------------------------------- *)

type tail_site = {
  ts_block : label;
  ts_args  : value list;
  ts_keep  : int;
      (** 从基本块头部保留的指令条数, Call 及之后的 Copy/Zext 链被删除 *)
}

(* 判断某个基本块是否是自递归尾调用点。
   入参: f_name 是当前函数名 (用于识别「调用自己」), bb 是要检查的基本块。
   逻辑: 从块末尾的 ret 返回值出发, 沿 Copy/Zext 链反向扫描到一条 call;
         只有「ret 的值 == 这条 self-call 的返回值」(中间最多隔着 Copy/Zext)
         才认定是尾调用, 否则 (遇到其它指令 / 非自递归 call / 返回值对不上) 返回 None。
         同时算出 ts_keep: call 之前需要保留的指令条数 (call 及之后的 Copy/Zext 会被删掉)。
   输出: Some tail_site (块号 / 实参 / 保留条数) 或 None。
   使用方: find_tail_sites 用它逐个扫描函数的所有基本块。 *)
let detect_tail_call (f_name : string) (bb : basic_block) : tail_site option =
  let n = List.length bb.bb_instrs in
  let rev_instrs = List.rev bb.bb_instrs in
  let rec scan rev depth target =
    match rev with
    | [] -> None
    | Call { dst; fn; args } :: _ when fn = f_name ->
      begin match target, dst with
      | None, None ->
        (* void 函数: Call(void) + Ret None *)
        Some { ts_block = bb.bb_label; ts_args = args; ts_keep = n - depth - 1 }
      | Some (VReg r), Some d when r = d ->
        (* int 函数: %d = Call(...); Ret(Some (VReg d)) *)
        Some { ts_block = bb.bb_label; ts_args = args; ts_keep = n - depth - 1 }
      | _ -> None
      end
    | (Copy { dst; src } | Zext { dst; src }) :: rest ->
      begin match target with
      | Some (VReg r) when r = dst -> scan rest (depth + 1) (Some src)
      | _ -> None
      end
    | _ :: _ -> None
  in
  match bb.bb_term with
  | Ret ret_val -> scan rev_instrs 0 ret_val
  | _ -> None

(* 收集一个函数里所有的自递归尾调用点。
   入参: f 是要分析的函数。
   逻辑: 对 f 的每个基本块调用 detect_tail_call (带上函数名), 用 filter_map 收集所有 Some。
   输出: tail_site 列表 (顺序与 f.f_blocks 的排列一致)。
   使用方: transform 据此判断函数是否需要做尾递归消除, 并拿到所有回边信息。 *)
let find_tail_sites (f : func) : tail_site list =
  List.filter_map (fun (_, bb) -> detect_tail_call f.f_name bb) f.f_blocks

(* ---- value 替换辅助 ---------------------------------------------------- *)

(* 用替换映射改写单个 value (递归穿透多级映射)。
   入参: repl 是 old_vreg → 新 value 的映射 (本 pass 里是「形参 vreg → 新 phi vreg」),
         v 是要改写的值。
   逻辑: 若 v 是 VReg r 且命中 repl, 就递归地换成映射值; Imm / Global 原样返回。
   输出: 改写后的 value。
   使用方: replace_instr / replace_term, 以及 transform 里构建 phi 回边实参时。 *)
let replace_value (repl : value IntMap.t) (v : value) : value =
  let rec resolve v =
    match v with
    | VReg r ->
      begin match IntMap.find_opt r repl with
      | Some v' -> resolve v'
      | None -> v
      end
    | Imm _ | Global _ -> v
  in
  resolve v

(* 用替换映射改写一条指令的所有 operand (不动 dst)。
   入参: repl 同 replace_value, i 是要改写的指令。
   逻辑: 遍历每条指令里的 value 字段 (load 的 ptr、store 的 val_/ptr、binop 的 lhs/rhs、
         phi 每个 incoming 的值、call 的 args 等), 逐个套 replace_value; dst 保持不变。
   输出: 改写后的指令。
   使用方: transform 里对入口块 / 尾调用块 / 其它块统一替换形参引用。 *)
let replace_instr (repl : value IntMap.t) (i : instr) : instr =
  let rv = replace_value repl in
  match i with
  | Alloca _ -> i
  | Load l   -> Load { l with ptr = rv l.ptr }
  | Store s  -> Store { val_ = rv s.val_; ptr = rv s.ptr }
  | Binop b  -> Binop { b with lhs = rv b.lhs; rhs = rv b.rhs }
  | Icmp c   -> Icmp { c with lhs = rv c.lhs; rhs = rv c.rhs }
  | Call c   -> Call { c with args = List.map rv c.args }
  | Phi p    -> Phi { p with incoming = List.map (fun (v, lbl) -> (rv v, lbl)) p.incoming }
  | Shl s    -> Shl { s with lhs = rv s.lhs; rhs = rv s.rhs }
  | AShr s   -> AShr { s with lhs = rv s.lhs; rhs = rv s.rhs }
  | And a    -> And { a with lhs = rv a.lhs; rhs = rv a.rhs }
  | Zext z   -> Zext { z with src = rv z.src }
  | Copy c   -> Copy { c with src = rv c.src }

(* 用替换映射改写终结指令里的 operand。
   入参: repl 同 replace_value, t 是要改写的终结指令。
   逻辑: ret 的返回值、br 的条件会被替换; jump 无 operand 原样返回。
   输出: 改写后的终结指令。
   使用方: transform 里对入口块 / 其它块替换终结指令中的形参引用。 *)
let replace_term (repl : value IntMap.t) (t : terminator) : terminator =
  let rv = replace_value repl in
  match t with
  | Ret (Some v) -> Ret (Some (rv v))
  | Ret None     -> Ret None
  | Br (cond, t, f) -> Br (rv cond, t, f)
  | Jump _       -> t

(* ---- 主变换 ------------------------------------------------------------ *)

(* 对单个函数做尾递归消除 (本 pass 的核心)。
   入参: f 是要变换的函数。
   逻辑: 先 find_tail_sites 找尾调用点; 若没有则原样返回 f。否则:
         1. 为每个形参分配一个新的 phi vreg, 建 old_vreg → 新 phi 的替换映射 repl;
         2. 构建循环头 phi: 入口边保留原始形参, 各尾调用回边用实参 (经 repl 替换形参引用);
         3. 新建一个入口块 new_entry → 原入口, 原入口变成循环头, f_entry 指向 new_entry;
         4. 尾调用块截断 call 及之后的 Copy/Zext, 终结指令改成 jmp 回循环头;
         5. 其余块只替换形参引用。
   输出: 变换后的函数 (f_blocks / f_entry / f_max_vreg / f_max_label 均已更新)。
   使用方: run_on_func。 *)
let transform (f : func) : func =
  let sites = find_tail_sites f in
  if List.length sites = 0 then f
  else
    let next_vreg = ref (f.f_max_vreg + 1) in
    let next_label = ref (f.f_max_label + 1) in
    let fresh_vreg () = let r = !next_vreg in incr next_vreg; r in
    let fresh_label () = let l = !next_label in incr next_label; l in

    let new_entry = fresh_label () in
    let old_entry = f.f_entry in

    (* 先为每个形参分配新 phi dst, 并据此构建 old_vreg → new_dst 替换映射 *)
    let param_dsts =
      List.map (fun (_, old_vreg) -> (old_vreg, fresh_vreg ())) f.f_params
    in
    let repl =
      List.fold_left (fun m (old, new_dst) ->
        IntMap.add old (VReg new_dst) m
      ) IntMap.empty param_dsts
    in

    (* 再构建 phi: 入口边保留原始形参, 回边用 repl 把形参引用换成当前循环值 *)
    let param_phis =
      List.mapi (fun i (old_vreg, new_dst) ->
        let from_new_entry = (VReg old_vreg, new_entry) in
        let from_tails =
          List.map (fun site ->
            (replace_value repl (List.nth site.ts_args i), site.ts_block)) sites
        in
        (old_vreg, Phi { dst = new_dst; incoming = from_new_entry :: from_tails })
      ) param_dsts
    in

    let phi_instrs = List.map snd param_phis in

    (* 标记 tail site block labels *)
    let tail_labels =
      List.fold_left (fun s site -> IntMap.add site.ts_block site s)
        IntMap.empty sites
    in

    let new_blocks =
      List.map (fun (lbl, bb) ->
        if lbl = old_entry then begin
          (* 旧入口块: 前插 phi 节点, 替换其余指令中的 value。
             若入口块本身也是尾调用块, 还需截断指令并把终结指令改成 Jump 自身,
             否则 phi 会丢失、新 phi dst 成为未定义 vreg。 *)
          let instrs =
            match IntMap.find_opt lbl tail_labels with
            | Some site -> List.filteri (fun i _ -> i < site.ts_keep) bb.bb_instrs
            | None -> bb.bb_instrs
          in
          let instrs = List.map (replace_instr repl) instrs in
          let term =
            match IntMap.find_opt lbl tail_labels with
            | Some _ -> Jump old_entry
            | None -> replace_term repl bb.bb_term
          in
          (lbl, { bb with bb_instrs = phi_instrs @ instrs; bb_term = term })
        end
        else match IntMap.find_opt lbl tail_labels with
        | Some site ->
          (* tail site: 截断指令, 替换 terminator 为 Jump old_entry *)
          let kept = List.filteri (fun i _ -> i < site.ts_keep) bb.bb_instrs in
          let kept = List.map (replace_instr repl) kept in
          (lbl, { bb with bb_instrs = kept; bb_term = Jump old_entry })
        | None ->
          (* 其他块: 替换 value *)
          let new_instrs = List.map (replace_instr repl) bb.bb_instrs in
          let new_term = replace_term repl bb.bb_term in
          (lbl, { bb with bb_instrs = new_instrs; bb_term = new_term })
      ) f.f_blocks
    in

    (* 新入口块: Jump old_entry *)
    let new_entry_block = {
      bb_label = new_entry;
      bb_instrs = [];
      bb_term = Jump old_entry;
    } in

    let all_blocks =
      List.sort (fun (a, _) (b, _) -> compare a b)
        ((new_entry, new_entry_block) :: new_blocks)
    in
    { f with f_blocks = all_blocks; f_entry = new_entry;
             f_max_vreg = !next_vreg - 1; f_max_label = !next_label - 1 }

(* ---- 顶层 -------------------------------------------------------------- *)

(* pass 对单函数的入口。
   入参: f 是要变换的函数。
   逻辑: 直接委托给 transform 完成尾递归消除。
   输出: 变换后的函数。
   使用方: run。 *)
let run_on_func (f : func) : func =
  transform f

(* pass 对模块的入口。
   入参: m 是整个模块。
   逻辑: 对 m_funcs 里的每个函数依次应用 run_on_func —— 尾递归消除是纯函数内变换,
         不跨函数, 也不改动全局变量。
   输出: 变换后的模块。
   使用方: 编译流水线 (bin/main.ml / bin/dump_ir.ml) 在常量折叠之后、内联之前调用。 *)
let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
