(* ToyC 优化 — 归纳变量化简 + 强度削减 (LLVM: -indvars / -loop-reduce)

   这个 pass 消费已经规范化过的 loop 形态

   这里复用 Loop_unroll.detect_counted_loop 提供的 canonical counted-loop
   信息：从 header phi 里识别 basic IV，再在整个循环体内查找形如 iv*a+b 的
   派生归纳变量，把每轮的乘法/移位链改成 preheader 初值 + 每个 latch 上的
   add/sub 递推。 *)

open Ir_types
open Common
open Loop_info

module U = Loop_unroll
module IntMap = U.IntMap
module IntSet = U.IntSet

type basic_iv = {
  iv   : int;
  init : value;
  step : int;
}

type affine = {
  iv : int option;
  a  : int;
  b  : int;
}

type derived_candidate = {
  dst       : int;
  aff       : affine;
}

(* 判断仿射表达式是否退化为常量。 *)
let is_const (e : affine) = e.a = 0

(* 构造常量仿射表达式。 *)
let affine_const (b : int) : affine = { iv = None; a = 0; b }

(* 组合两个仿射表达式的乘法。 *)
let affine_mul (e1 : affine) (e2 : affine) : affine option =
  if is_const e1 then Some { e2 with a = e2.a * e1.b; b = e2.b * e1.b }
  else if is_const e2 then Some { e1 with a = e1.a * e2.b; b = e1.b * e2.b }
  else None

(* 组合两个仿射表达式的加法。 *)
let affine_add (e1 : affine) (e2 : affine) : affine option =
  match e1.iv, e2.iv with
  | None, _ -> Some { e2 with b = e1.b + e2.b }
  | _, None -> Some { e1 with b = e1.b + e2.b }
  | Some x, Some y when x = y -> Some { iv = Some x; a = e1.a + e2.a; b = e1.b + e2.b }
  | _ -> None

(* 组合两个仿射表达式的减法。 *)
let affine_sub (e1 : affine) (e2 : affine) : affine option =
  match e1.iv, e2.iv with
  | None, None -> Some (affine_const (e1.b - e2.b))
  | None, Some y -> Some { iv = Some y; a = -e2.a; b = e1.b - e2.b }
  | Some x, None -> Some { iv = Some x; a = e1.a; b = e1.b - e2.b }
  | Some x, Some y when x = y -> Some { iv = Some x; a = e1.a - e2.a; b = e1.b - e2.b }
  | _ -> None

(* 尝试把值 v 识别为 iv*a+b 形式的仿射表达式。 *)
let rec affine_of_value (defs : instr IntMap.t) (basic_ivs : IntSet.t) (v : value)
    : affine option =
  match v with
  | Imm b -> Some (affine_const b)
  | VReg r when IntSet.mem r basic_ivs -> Some { iv = Some r; a = 1; b = 0 }
  | VReg r ->
      (match IntMap.find_opt r defs with
       | Some (Copy { src; _ }) -> affine_of_value defs basic_ivs src
       | Some (Binop { op = Mul; lhs; rhs; _ }) ->
           (match affine_of_value defs basic_ivs lhs,
                  affine_of_value defs basic_ivs rhs with
            | Some e1, Some e2 -> affine_mul e1 e2
            | _ -> None)
       | Some (Binop { op = Add; lhs; rhs; _ }) ->
           (match affine_of_value defs basic_ivs lhs,
                  affine_of_value defs basic_ivs rhs with
            | Some e1, Some e2 -> affine_add e1 e2
            | _ -> None)
       | Some (Binop { op = Sub; lhs; rhs; _ }) ->
           (match affine_of_value defs basic_ivs lhs,
                  affine_of_value defs basic_ivs rhs with
            | Some e1, Some e2 -> affine_sub e1 e2
            | _ -> None)
       | Some (Shl { lhs; rhs = Imm k; _ }) ->
           (match affine_of_value defs basic_ivs lhs with
            | Some e -> Some { e with a = e.a * (1 lsl k); b = e.b * (1 lsl k) }
            | None -> None)
       | _ -> None)
  | Global _ -> None

let build_loop_instrs (bmap : basic_block IntMap.t) (lp : loop)
    : (label * instr list) list =
  IntSet.elements lp.blocks
  |> List.map (fun lbl ->
       let bb = IntMap.find lbl bmap in
       if lbl = lp.header then
         let _, rest = U.partition_header_instrs bb in
         (lbl, rest)
       else
         (lbl, bb.bb_instrs))

let has_unsupported_instrs (loop_instrs : (label * instr list) list) =
  List.exists (fun (_, instrs) ->
    List.exists (function Alloca _ | Phi _ -> true | _ -> false) instrs
  ) loop_instrs

(* 从 canonical counted loop 的 header phi 中识别基本归纳变量。 *)
let detect_basic_ivs (loop_defs : instr IntMap.t) (spec : U.counted_loop) : basic_iv list =
  List.filter_map (fun (phi : U.phi_info) ->
    let steps =
      List.map (fun (_, latch_v) ->
        match U.extract_step loop_defs phi.dst latch_v with
        | Some step when step <> 0 -> Some step
        | _ -> None
      ) phi.latch_incomings
    in
    match phi.init, steps with
    | init, Some step :: rest when List.for_all (( = ) (Some step)) rest ->
        Some { iv = phi.dst; init; step }
    | _ ->
        None
  ) spec.phis

let collect_candidates
    (loop_instrs : (label * instr list) list)
    (loop_defs : instr IntMap.t)
    (basic_iv_set : IntSet.t) : derived_candidate list =
  List.concat_map (fun (_lbl, instrs) ->
    List.filter_map (fun instr ->
      match instr_dst instr with
      | None ->
          None
      | Some dst ->
          match affine_of_value loop_defs basic_iv_set (VReg dst) with
          | Some aff when aff.iv <> None && aff.a <> 0 && abs aff.a > 1 ->
              Some { dst; aff }
          | _ ->
              None
    ) instrs
  ) loop_instrs

(* 生成 preheader 中计算 a*init+b 的指令，返回最终 value。 *)
let emit_affine_init (fresh : unit -> int) (pre_instrs : instr list ref)
    (init : value) (a : int) (b : int) : value =
  let emit i = pre_instrs := i :: !pre_instrs in
  if a = 0 then Imm b
  else if a = 1 then begin
    if b = 0 then init
    else
      let d = fresh () in
      emit (Binop { dst = d; op = Add; lhs = init; rhs = Imm b });
      VReg d
  end
  else begin
    let d1 = fresh () in
    emit (Binop { dst = d1; op = Mul; lhs = init; rhs = Imm a });
    if b = 0 then VReg d1
    else
      let d2 = fresh () in
      if b > 0 then
        emit (Binop { dst = d2; op = Add; lhs = VReg d1; rhs = Imm b })
      else
        emit (Binop { dst = d2; op = Sub; lhs = VReg d1; rhs = Imm (-b) });
      VReg d2
  end

let emit_affine_step (dst : int) (src : value) (delta : int) : instr =
  if delta >= 0 then
    Binop { dst; op = Add; lhs = src; rhs = Imm delta }
  else
    Binop { dst; op = Sub; lhs = src; rhs = Imm (-delta) }

let append_latch_instr
    (latch_instrs : instr list IntMap.t ref) (latch : label) (instr : instr) =
  let prev = Option.value ~default:[] (IntMap.find_opt latch !latch_instrs) in
  latch_instrs := IntMap.add latch (prev @ [ instr ]) !latch_instrs

(* 对单个循环应用归纳变量强度削减。 *)
let apply_indvars (f : func) (bmap : basic_block IntMap.t) (lp : loop)
    : (basic_block IntMap.t * int) option =
  match U.detect_counted_loop bmap lp with
  | None ->
      None
  | Some spec ->
      let loop_instrs = build_loop_instrs bmap lp in
      if has_unsupported_instrs loop_instrs then None
      else begin
        let loop_defs = U.build_loop_defs bmap lp in
        let basic_ivs = detect_basic_ivs loop_defs spec in
        let basic_iv_set =
          IntSet.of_list (List.map (fun (b : basic_iv) -> b.iv) basic_ivs)
        in
        let raw_candidates = collect_candidates loop_instrs loop_defs basic_iv_set in
        if raw_candidates = [] then None
        else begin
          let next_vreg = ref (f.f_max_vreg + 1) in
          let fresh_vreg () = let x = !next_vreg in incr next_vreg; x in
          let pre_instrs = ref [] in
          let new_phis = ref [] in
          let latch_instrs = ref IntMap.empty in
          let phi_map = ref IntMap.empty in

          List.iter (fun ({ dst; aff } : derived_candidate) ->
            match aff.iv with
            | None ->
                ()
            | Some iv ->
                match List.find_opt (fun (b : basic_iv) -> b.iv = iv) basic_ivs with
                | None ->
                    ()
                | Some basic ->
                    let a = aff.a and b = aff.b in
                    let delta = a * basic.step in
                    let phi_dst = fresh_vreg () in
                    let init_val =
                      emit_affine_init fresh_vreg pre_instrs basic.init a b in
                    let latch_incomings =
                      List.map (fun latch ->
                        let next_dst = fresh_vreg () in
                        append_latch_instr latch_instrs latch
                          (emit_affine_step next_dst (VReg phi_dst) delta);
                        (VReg next_dst, latch)
                      ) spec.latches
                    in
                    new_phis := Phi {
                      dst = phi_dst;
                      incoming = (init_val, spec.preheader) :: latch_incomings;
                    } :: !new_phis;
                    phi_map := IntMap.add dst phi_dst !phi_map
          ) raw_candidates;

          if IntMap.is_empty !phi_map then None
          else begin
            let rewrite_instr instr =
              match instr_dst instr with
              | Some dst when IntMap.mem dst !phi_map ->
                  Copy { dst; src = VReg (IntMap.find dst !phi_map) }
              | _ ->
                  instr
            in
            let bmap =
              IntMap.mapi (fun lbl bb ->
                if lbl = spec.preheader then
                  { bb with bb_instrs = bb.bb_instrs @ List.rev !pre_instrs }
                else if IntSet.mem lbl lp.blocks then
                  let block_incs =
                    Option.value ~default:[] (IntMap.find_opt lbl !latch_instrs)
                  in
                  if lbl = lp.header then
                    let header_phis, header_rest = U.partition_header_instrs bb in
                    { bb with
                      bb_instrs =
                        header_phis
                        @ List.rev !new_phis
                        @ List.map rewrite_instr header_rest
                        @ block_incs }
                  else
                    { bb with
                      bb_instrs = List.map rewrite_instr bb.bb_instrs @ block_incs }
                else
                  bb
              ) bmap
            in
            Some (bmap, !next_vreg - 1)
          end
        end
      end

(* 逐函数反复运行 indvars 直到无可优化。 *)
let run_on_func (f : func) : func =
  let rec fixpoint (f : func) : func =
    let bmap = U.build_bmap f in
    let dom = Dominance.analyze f in
    let li = analyze f dom in
    let loops =
      List.sort (fun a b ->
        let c = compare b.depth a.depth in
        if c <> 0 then c else compare a.header b.header
      ) li.loops
    in
    match List.find_map (apply_indvars f bmap) loops with
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

(* 模块入口。 *)
let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
