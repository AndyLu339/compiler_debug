(* ToyC 代码生成 — IR -> RISC-V assembly
   使用 Regalloc 提供的寄存器分配结果 *)

open Common
open Ir_types
open Regalloc

module IntMap = Map.Make (Int)
module StringMap = Map.Make (String)

let riscv_arg_regs = [| "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7" |]

(* ---- RISC-V 汇编输出辅助 ---- *)

let emit b s = Buffer.add_string b ("\t" ^ s ^ "\n")
let emit_label b s = Buffer.add_string b (s ^ ":\n")

let is_imm12 n = n >= -2048 && n <= 2047

let label_of f_name bb =
  Printf.sprintf ".L_%s_bb%d" f_name bb

let load_imm b rd n =
  if n = 0 then emit b (Printf.sprintf "mv %s, zero" rd)
  else emit b (Printf.sprintf "li %s, %d" rd n)

let load_addr b rd name =
  emit b (Printf.sprintf "la %s, %s" rd name)

let load_word b rd offset base =
  emit b (Printf.sprintf "lw %s, %d(%s)" rd offset base)

let store_word b rs offset base =
  emit b (Printf.sprintf "sw %s, %d(%s)" rs offset base)

let emit_epilogue b fa =
  List.iter (fun (reg, offset) -> load_word b reg offset "sp") fa.saved_regs;
  if fa.save_ra then load_word b "ra" fa.ra_offset "sp";
  if fa.frame_size > 0 then
    emit b (Printf.sprintf "addi sp, sp, %d" fa.frame_size);
  emit b "ret"

(* ---- 寄存器分配查询 ---- *)

(* 两个临时寄存器，用于中间计算（不在可分配池中） *)
let scratch1 = "t5"
let scratch2 = "t6"

let vreg_loc fa r =
  try IntMap.find r fa.vreg_loc
  with Not_found ->
    failwith (Printf.sprintf "codegen: no location for %%r%d" r)

let alloca_off fa r =
  try IntMap.find r fa.allocas
  with Not_found ->
    failwith (Printf.sprintf "codegen: %%r%d is not an alloca" r)

(* 将寄存器 rs 的值存回 vreg r 的位置 *)
let store_to_vreg b fa rs r =
  match vreg_loc fa r with
  | Reg reg ->
    if rs <> reg then emit b (Printf.sprintf "mv %s, %s" reg rs)
  | Stack offset ->
    store_word b rs offset "sp"

(* 将 vreg r 的值加载到寄存器 rd *)
let load_from_vreg b fa rd r =
  (* VReg(-1) 是 mem2reg 的 undef 哨兵，代表循环内声明变量在 pre-header
     路径上的缺失值。它无活跃区间、未分配寄存器，且不会被实际读取 —
     相关 phi 的入口边永不执行。此处不做任何操作，仅防下游 crash。 *)
  if r < 0 then ()
  else match vreg_loc fa r with
  | Reg reg ->
    if rd <> reg then emit b (Printf.sprintf "mv %s, %s" rd reg)
  | Stack offset ->
    load_word b rd offset "sp"

(* 将任意值（Imm 或 VReg）materalize 到寄存器 rd *)
let materialize_value b fa rd = function
  | Imm n ->
    load_imm b rd n
  | Global name ->
    load_addr b rd name
  | VReg r ->
    if IntMap.mem r fa.allocas then
      (* alloca vreg 的值是栈地址指针 *)
      emit b (Printf.sprintf "addi %s, sp, %d" rd (alloca_off fa r))
    else
      load_from_vreg b fa rd r

(* 将指针值 materialize 到寄存器 rd *)
let materialize_ptr b fa rd = function
  | VReg r when IntMap.mem r fa.allocas ->
    emit b (Printf.sprintf "addi %s, sp, %d" rd (alloca_off fa r))
  | VReg r ->
    load_from_vreg b fa rd r
  | Global name ->
    load_addr b rd name
  | Imm n ->
    load_imm b rd n

(* ---- 指令发射 ---- *)

let emit_copy_to_vreg b fa dst src =
  match vreg_loc fa dst with
  | Reg dreg ->
    materialize_value b fa dreg src
  | Stack offset ->
    materialize_value b fa scratch1 src;
    store_word b scratch1 offset "sp"

let riscv_op_name = function
  | Add -> "add"  | Sub -> "sub"  | Mul -> "mul"
  | Div -> "div"  | Mod -> "rem"
  | _ -> failwith "unexpected binop in riscv_op_name"

let emit_binop b fa dst op lhs rhs =
  let finish rd_dst =
    (* 源操作数优先直接用物理寄存器，避免多余 mv (如 i*i → mul rd, t0, t0) *)
    let op_reg v scratch =
      match v with
      | VReg r when not (IntMap.mem r fa.allocas) ->
        (match vreg_loc fa r with
         | Reg reg -> reg
         | Stack _ -> materialize_value b fa scratch v; scratch)
      | _ -> materialize_value b fa scratch v; scratch
    in
    let rl = op_reg lhs scratch1 in
    let rr = op_reg rhs scratch2 in
    emit b (Printf.sprintf "%s %s, %s, %s" (riscv_op_name op) rd_dst rl rr)
  in
  match op, vreg_loc fa dst with
  (* --- addi 优化 --- *)
  | Add, Reg dreg when
      (match lhs, rhs with
       | _, Imm n when is_imm12 n -> true
       | Imm n, _ when is_imm12 n -> true
       | _ -> false) ->
    begin match lhs, rhs with
    | lhs, Imm n when is_imm12 n ->
      materialize_value b fa dreg lhs;
      emit b (Printf.sprintf "addi %s, %s, %d" dreg dreg n)
    | Imm n, rhs when is_imm12 n ->
      materialize_value b fa dreg rhs;
      emit b (Printf.sprintf "addi %s, %s, %d" dreg dreg n)
    | _ -> assert false
    end
  | Add, Stack offset when
      (match lhs, rhs with
       | _, Imm n when is_imm12 n -> true
       | Imm n, _ when is_imm12 n -> true
       | _ -> false) ->
    begin match lhs, rhs with
    | lhs, Imm n when is_imm12 n ->
      materialize_value b fa scratch1 lhs;
      emit b (Printf.sprintf "addi %s, %s, %d" scratch1 scratch1 n);
      store_word b scratch1 offset "sp"
    | Imm n, rhs when is_imm12 n ->
      materialize_value b fa scratch1 rhs;
      emit b (Printf.sprintf "addi %s, %s, %d" scratch1 scratch1 n);
      store_word b scratch1 offset "sp"
    | _ -> assert false
    end
  (* --- sub -> addi 优化 --- *)
  | Sub, Reg dreg when
      (match lhs, rhs with
       | _, Imm n when is_imm12 (-n) -> true
       | _ -> false) ->
    begin match lhs, rhs with
    | lhs, Imm n ->
      materialize_value b fa dreg lhs;
      emit b (Printf.sprintf "addi %s, %s, %d" dreg dreg (-n))
    | _ -> assert false
    end
  | Sub, Stack offset when
      (match lhs, rhs with
       | _, Imm n when is_imm12 (-n) -> true
       | _ -> false) ->
    begin match lhs, rhs with
    | lhs, Imm n ->
      materialize_value b fa scratch1 lhs;
      emit b (Printf.sprintf "addi %s, %s, %d" scratch1 scratch1 (-n));
      store_word b scratch1 offset "sp"
    | _ -> assert false
    end
  (* Eq/Ne/Lt/Gt/Le/Ge/LAnd/LOr 的 Binop 不会出现：
     irgen 把比较翻译为 Icmp，把 &&/|| 翻译为短路 phi。
     这里仅处理 Add/Sub/Mul/Div/Mod 的三操作数形式。 *)
  (* --- 默认: 三操作数运算到寄存器 --- *)
  | _, Reg dreg ->
    finish dreg
  | _, Stack offset ->
    finish scratch1;
    store_word b scratch1 offset "sp"

let emit_icmp b fa dst cond lhs rhs =
  (* lhs 直接物化到结果寄存器 rd，rhs 物化到 scratch2，省去一次 scratch1 中转 *)
  let emit_cmp_in_reg rd =
    match cond with
    | IEq ->
      begin match rhs with
      | Imm 0 ->
        materialize_value b fa rd lhs;
        emit b (Printf.sprintf "seqz %s, %s" rd rd)
      | _ ->
        materialize_value b fa rd lhs;
        materialize_value b fa scratch2 rhs;
        emit b (Printf.sprintf "sub %s, %s, %s" rd rd scratch2);
        emit b (Printf.sprintf "seqz %s, %s" rd rd)
      end
    | INe ->
      begin match rhs with
      | Imm 0 ->
        materialize_value b fa rd lhs;
        emit b (Printf.sprintf "snez %s, %s" rd rd)
      | _ ->
        materialize_value b fa rd lhs;
        materialize_value b fa scratch2 rhs;
        emit b (Printf.sprintf "sub %s, %s, %s" rd rd scratch2);
        emit b (Printf.sprintf "snez %s, %s" rd rd)
      end
    | ISlt ->
      begin match rhs with
      | Imm n when is_imm12 n ->
        materialize_value b fa rd lhs;
        emit b (Printf.sprintf "slti %s, %s, %d" rd rd n)
      | _ ->
        materialize_value b fa rd lhs;
        materialize_value b fa scratch2 rhs;
        emit b (Printf.sprintf "slt %s, %s, %s" rd rd scratch2)
      end
    | ISle ->
      materialize_value b fa rd lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "slt %s, %s, %s" rd scratch2 rd);
      emit b (Printf.sprintf "xori %s, %s, 1" rd rd)
    | ISgt ->
      materialize_value b fa rd lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "slt %s, %s, %s" rd scratch2 rd)
    | ISge ->
      materialize_value b fa rd lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "slt %s, %s, %s" rd rd scratch2);
      emit b (Printf.sprintf "xori %s, %s, 1" rd rd)
  in
  match vreg_loc fa dst with
  | Reg dreg -> emit_cmp_in_reg dreg
  | Stack offset ->
    emit_cmp_in_reg scratch1;
    store_word b scratch1 offset "sp"

let emit_call b fa dst fn args =
  List.iteri
    (fun i arg ->
       materialize_value b fa scratch1 arg;
       if i < 8 then
         emit b (Printf.sprintf "mv %s, %s" riscv_arg_regs.(i) scratch1)
       else
         store_word b scratch1 (4 * (i - 8)) "sp")
    args;
  emit b (Printf.sprintf "call %s" fn);
  match dst with
  | None -> ()
  | Some r -> store_to_vreg b fa "a0" r

let emit_instr b fa = function
  | Alloca _ ->
    ()
  | Load { dst; ptr } ->
    materialize_ptr b fa scratch1 ptr;
    load_word b scratch2 0 scratch1;
    store_to_vreg b fa scratch2 dst
  | Store { val_; ptr } ->
    materialize_value b fa scratch1 val_;
    materialize_ptr b fa scratch2 ptr;
    store_word b scratch1 0 scratch2
  | Binop { dst; op; lhs; rhs } ->
    emit_binop b fa dst op lhs rhs
  | Icmp { dst; cond; lhs; rhs } ->
    emit_icmp b fa dst cond lhs rhs
  | Call { dst; fn; args } ->
    emit_call b fa dst fn args
  | Phi _ ->
    ()
  | Shl { dst; lhs; rhs } ->
    begin match rhs, vreg_loc fa dst with
    | Imm n, Reg dreg when n >= 0 && n < 32 ->
      materialize_value b fa dreg lhs;
      emit b (Printf.sprintf "slli %s, %s, %d" dreg dreg n)
    | Imm n, Stack offset when n >= 0 && n < 32 ->
      materialize_value b fa scratch1 lhs;
      emit b (Printf.sprintf "slli %s, %s, %d" scratch1 scratch1 n);
      store_word b scratch1 offset "sp"
    | _, Reg dreg ->
      materialize_value b fa dreg lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "sll %s, %s, %s" dreg dreg scratch2)
    | _, Stack offset ->
      materialize_value b fa scratch1 lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "sll %s, %s, %s" scratch1 scratch1 scratch2);
      store_word b scratch1 offset "sp"
    end
  | AShr { dst; lhs; rhs } ->
    begin match rhs, vreg_loc fa dst with
    | Imm n, Reg dreg when n >= 0 && n < 32 ->
      materialize_value b fa dreg lhs;
      emit b (Printf.sprintf "srai %s, %s, %d" dreg dreg n)
    | Imm n, Stack offset when n >= 0 && n < 32 ->
      materialize_value b fa scratch1 lhs;
      emit b (Printf.sprintf "srai %s, %s, %d" scratch1 scratch1 n);
      store_word b scratch1 offset "sp"
    | _, Reg dreg ->
      materialize_value b fa dreg lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "sra %s, %s, %s" dreg dreg scratch2)
    | _, Stack offset ->
      materialize_value b fa scratch1 lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "sra %s, %s, %s" scratch1 scratch1 scratch2);
      store_word b scratch1 offset "sp"
    end
  | And { dst; lhs; rhs } ->
    begin match rhs, vreg_loc fa dst with
    | Imm n, Reg dreg when is_imm12 n ->
      materialize_value b fa dreg lhs;
      emit b (Printf.sprintf "andi %s, %s, %d" dreg dreg n)
    | Imm n, Stack offset when is_imm12 n ->
      materialize_value b fa scratch1 lhs;
      emit b (Printf.sprintf "andi %s, %s, %d" scratch1 scratch1 n);
      store_word b scratch1 offset "sp"
    | _, Reg dreg ->
      materialize_value b fa dreg lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "and %s, %s, %s" dreg dreg scratch2)
    | _, Stack offset ->
      materialize_value b fa scratch1 lhs;
      materialize_value b fa scratch2 rhs;
      emit b (Printf.sprintf "and %s, %s, %s" scratch1 scratch1 scratch2);
      store_word b scratch1 offset "sp"
    end
  | Zext { dst; src } ->
    materialize_value b fa scratch1 src;
    emit b (Printf.sprintf "andi %s, %s, 1" scratch1 scratch1);
    store_to_vreg b fa scratch1 dst
  | Copy { dst; src } ->
    emit_copy_to_vreg b fa dst src

(* ---- 比较 → 条件分支融合 ----
   当 icmp 的结果仅被紧随其后的 Br 使用时，跳过 0/1 物化，直接生成条件分支。
   这可省去 `slt/seqz + beqz` 序列，直接得到 `bne/beq/blt/bge`。 *)

(* 统计每个 vreg 作为 operand 被使用的次数 *)
let use_count_map (f : func) : int IntMap.t =
  let counts = ref IntMap.empty in
  let add = function
    | VReg r ->
      counts := IntMap.update r
        (function None -> Some 1 | Some n -> Some (n + 1)) !counts
    | _ -> ()
  in
  List.iter (fun (_, bb) ->
    List.iter (fun instr -> List.iter add (instr_uses instr)) bb.bb_instrs;
    List.iter add (terminator_uses bb.bb_term)
  ) f.f_blocks;
  !counts

(* 找出可融合的 icmp: 块内最后一条指令是 Icmp，且其 dst 仅被本块 Br 的 cond 使用 *)
let fused_icmp (f : func) : (icmp_cond * value * value) IntMap.t =
  let uses = use_count_map f in
  let fused = ref IntMap.empty in
  List.iter (fun (_, bb) ->
    match List.rev bb.bb_instrs with
    | Icmp { dst; cond; lhs; rhs } :: _ ->
      begin match bb.bb_term with
      | Br (VReg r, _, _) when r = dst && IntMap.find_opt dst uses = Some 1 ->
        fused := IntMap.add dst (cond, lhs, rhs) !fused
      | _ -> ()
      end
    | _ -> ()
  ) f.f_blocks;
  !fused

(* 发射条件分支: cond 为假时跳转到 false_label *)
let emit_cond_branch b fa cond lhs rhs false_label =
  let branch_op = match cond with
    | IEq  -> "bne"   (* a==b 走 true;  a!=b 跳 false *)
    | INe  -> "beq"   (* a!=b 走 true;  a==b 跳 false *)
    | ISlt -> "bge"   (* a<b  走 true;  a>=b 跳 false *)
    | ISle -> "bgt"   (* a<=b 走 true;  a>b  跳 false *)
    | ISgt -> "ble"   (* a>b  走 true;  a<=b 跳 false *)
    | ISge -> "blt"   (* a>=b 走 true;  a<b  跳 false *)
  in
  (* 操作数优先直接用物理寄存器; Imm 0 直接引用 zero; 否则物化到 scratch *)
  let emit_operand v scratch =
    match v with
    | Imm 0 -> "zero"
    | VReg r when not (IntMap.mem r fa.allocas) ->
      (match vreg_loc fa r with
       | Reg reg -> reg
       | Stack _ -> materialize_value b fa scratch v; scratch)
    | _ -> materialize_value b fa scratch v; scratch
  in
  let rl = emit_operand lhs scratch1 in
  let rr = emit_operand rhs scratch2 in
  emit b (Printf.sprintf "%s %s, %s, %s" branch_op rl rr false_label)

(* ---- 控制流 ---- *)

let phi_incomings_for succ pred =
  List.fold_left
    (fun acc instr ->
       match instr with
       | Phi { dst; incoming } ->
         begin match List.find_opt (fun (_, lbl) -> lbl = pred) incoming with
         | Some (v, _) -> (dst, v) :: acc
         | None -> acc
         end
       | _ -> acc)
    [] succ.bb_instrs
  |> List.rev

(* phi 并行拷贝的 move：src 已解析为可发射的形式 *)
type phi_src =
  | PSImm of int
  | PSGlobal of string
  | PSReg of string
  | PSStack of int

type phi_move = { mid : int; mdst : string; msrc : phi_src }

let emit_phi_copies b fa copies =
  (* phi 语义是所有赋值同时发生，每个 dst 拿到 src 的旧值。
     这里用 Briggs/Appel 的 move 顺序化：
     1) dst 在栈的 copy 先落地（写栈不覆盖寄存器，读到的必是旧值）；
     2) dst 在寄存器的 copy 用寄存器中转，仅在成环时用 scratch1 破环。 *)
  let copies =
    List.filter (fun (_, src) ->
      match src with
      | VReg r when r < 0 -> false
      | _ -> true) copies
  in

  (* 1) dst 在栈的 copy *)
  List.iter (fun (dst, src) ->
    match vreg_loc fa dst with
    | Stack doff ->
      (match src with
       | VReg r ->
         (match vreg_loc fa r with
          | Reg sreg -> store_word b sreg doff "sp"
          | Stack soff ->
            load_word b scratch1 soff "sp";
            store_word b scratch1 doff "sp")
       | _ ->
         materialize_value b fa scratch1 src;
         store_word b scratch1 doff "sp")
    | Reg _ -> ()) copies;

  (* 2) dst 在寄存器的 move 集合 *)
  let next_id = ref 0 in
  let moves =
    List.filter_map (fun (dst, src) ->
      match vreg_loc fa dst with
      | Reg dreg ->
        let sd =
          match src with
          | Imm n -> PSImm n
          | Global g -> PSGlobal g
          | VReg r ->
            (match vreg_loc fa r with
             | Reg sreg -> PSReg sreg
             | Stack soff -> PSStack soff)
        in
        (* 自拷贝（源寄存器 == 目标寄存器）无需任何操作，跳过以免被环检测误判 *)
        (match sd with
         | PSReg sreg when sreg = dreg -> None
         | _ ->
           let id = !next_id in incr next_id;
           Some { mid = id; mdst = dreg; msrc = sd })
      | Stack _ -> None) copies
  in

  let emit_move m =
    match m.msrc with
    | PSImm n -> load_imm b m.mdst n
    | PSGlobal g -> load_addr b m.mdst g
    | PSStack soff -> load_word b m.mdst soff "sp"
    | PSReg sreg ->
      if sreg <> m.mdst then emit b (Printf.sprintf "mv %s, %s" m.mdst sreg)
  in

  let moves = ref moves in
  let rec drain () =
    match !moves with
    | [] -> ()
    | _ ->
      let src_regs =
        List.filter_map (fun m ->
          match m.msrc with PSReg s -> Some s | _ -> None) !moves
      in
      let safe = List.find_opt (fun m -> not (List.mem m.mdst src_regs)) !moves in
      match safe with
      | Some m ->
        moves := List.filter (fun x -> x.mid <> m.mid) !moves;
        emit_move m;
        drain ()
      | None ->
        (* 所有剩余 move 的 dst 都被读取 → 成环，任取一个寄存器源 move 破环 *)
        let m = List.find (fun x -> match x.msrc with PSReg _ -> true | _ -> false) !moves in
        (match m.msrc with
         | PSReg sreg ->
           emit b (Printf.sprintf "mv %s, %s" scratch1 sreg);
           moves := List.map (fun x ->
             if x.mid = m.mid then { x with msrc = PSReg scratch1 } else x) !moves;
           drain ()
         | _ -> assert false)
  in
  drain ()

let block_map f =
  List.fold_left (fun m (lbl, bb) -> IntMap.add lbl bb m) IntMap.empty f.f_blocks

let emit_edge b fa blocks f_name pred succ_lbl =
  let succ = IntMap.find succ_lbl blocks in
  let copies = phi_incomings_for succ pred in
  emit_phi_copies b fa copies;
  emit b (Printf.sprintf "j %s" (label_of f_name succ_lbl))

let emit_terminator b fa blocks f_name pred fused = function
  | Ret None ->
      emit_epilogue b fa
  | Ret (Some v) ->
    materialize_value b fa "a0" v;
      emit_epilogue b fa
  | Jump lbl ->
    emit_edge b fa blocks f_name pred lbl
  | Br (cond, t_lbl, f_lbl) ->
    let false_copy_label =
      Printf.sprintf ".L_%s_edge_%d_%d" f_name pred f_lbl
    in
    begin match cond with
    | VReg r when IntMap.mem r fused ->
      let (icond, lhs, rhs) = IntMap.find r fused in
      emit_cond_branch b fa icond lhs rhs false_copy_label
    | _ ->
      materialize_value b fa scratch1 cond;
      emit b (Printf.sprintf "beqz %s, %s" scratch1 false_copy_label)
    end;
    emit_edge b fa blocks f_name pred t_lbl;
    emit_label b false_copy_label;
    emit_edge b fa blocks f_name pred f_lbl

(* ---- 函数发射 ---- *)

let emit_prologue b fa =
  if fa.frame_size > 0 then
    emit b (Printf.sprintf "addi sp, sp, -%d" fa.frame_size);
  if fa.save_ra then
    store_word b "ra" fa.ra_offset "sp";
  List.iter (fun (reg, offset) -> store_word b reg offset "sp") fa.saved_regs

let emit_params b fa f =
  List.iteri
    (fun i (_, r) ->
       if i < 8 then
         store_to_vreg b fa riscv_arg_regs.(i) r
       else
         let caller_arg_offset = fa.frame_size + (4 * (i - 8)) in
         load_word b scratch1 caller_arg_offset "sp";
         store_to_vreg b fa scratch1 r)
    f.f_params

let emit_func b f fa =
  let blocks = block_map f in
  let fused = fused_icmp f in
  let ordered_blocks =
    let entry_block = List.filter (fun (lbl, _) -> lbl = f.f_entry) f.f_blocks in
    let other_blocks = List.filter (fun (lbl, _) -> lbl <> f.f_entry) f.f_blocks in
    entry_block @ other_blocks
  in
  Buffer.add_string b "\t.text\n";
  Buffer.add_string b (Printf.sprintf "\t.globl %s\n" f.f_name);
  Buffer.add_string b (Printf.sprintf "\t.type %s, @function\n" f.f_name);
  emit_label b f.f_name;
  emit_prologue b fa;
  emit_params b fa f;
  List.iter
    (fun (lbl, bb) ->
       emit_label b (label_of f.f_name lbl);
       List.iter
         (fun instr ->
            match instr with
            | Icmp { dst; _ } when IntMap.mem dst fused -> ()  (* 融合: 跳过 icmp 物化 *)
            | _ -> emit_instr b fa instr)
         bb.bb_instrs;
       emit_terminator b fa blocks f.f_name lbl fused bb.bb_term)
    ordered_blocks;
  Buffer.add_string b (Printf.sprintf "\t.size %s, .-%s\n\n" f.f_name f.f_name)

(* ---- 全局变量 ---- *)

let emit_global b = function
  | GVar { name; init } ->
    Buffer.add_string b "\t.data\n";
    Buffer.add_string b "\t.align 2\n";
    Buffer.add_string b (Printf.sprintf "\t.globl %s\n" name);
    emit_label b name;
    emit b (Printf.sprintf ".word %d" init)
  | GConst { name; value } ->
    Buffer.add_string b "\t.section .rodata\n";
    Buffer.add_string b "\t.align 2\n";
    Buffer.add_string b (Printf.sprintf "\t.globl %s\n" name);
    emit_label b name;
    emit b (Printf.sprintf ".word %d" value)

(* ---- 入口 ---- *)

let generate (m : module_) (alloc : alloc_result) : string =
  let b = Buffer.create 4096 in
  List.iter (emit_global b) m.m_globals;
  if m.m_globals <> [] then Buffer.add_char b '\n';
  List.iter (fun (name, f) ->
    let fa =
      try StringMap.find name alloc
      with Not_found ->
        failwith (Printf.sprintf "codegen: no alloc info for %s" name)
    in
    emit_func b f fa
  ) m.m_funcs;
  Buffer.contents b
