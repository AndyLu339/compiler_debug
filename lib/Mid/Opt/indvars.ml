(* ToyC 优化 — 归纳变量化简 + 强度削减 (LLVM: -indvars / -loop-reduce)

   识别 header phi 作为 basic IV，并在循环体中识别形如 iv*a+b 的派生归纳变量，
   把每轮的乘法/移位链改成 preheader 初值 + 每轮 add 步长。 *)

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

(* 把指令列表转换为 dst vreg -> 定义指令 的映射。 *)
let build_body_defs (instrs : instr list) : instr IntMap.t =
  List.fold_left (fun m instr ->
    match instr_dst instr with
    | Some dst -> IntMap.add dst instr m
    | None -> m
  ) IntMap.empty instrs

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

(* 从 header phi 中识别基本归纳变量。 *)
let detect_basic_ivs (header_phis : instr list) (preheader : label) (latch : label)
    (body_defs : instr IntMap.t) : basic_iv list =
  List.filter_map (function
    | Phi { dst; incoming; _ } ->
        (match U.find_incoming preheader incoming, U.find_incoming latch incoming with
         | Some init, Some latch_v ->
             (match U.extract_step body_defs dst latch_v with
              | Some step when step <> 0 -> Some { iv = dst; init; step }
              | _ -> None)
         | _ -> None)
    | _ -> None
  ) header_phis

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

(* 对单个循环应用归纳变量强度削减。 *)
let apply_indvars (f : func) (bmap : basic_block IntMap.t) (lp : loop)
    : (basic_block IntMap.t * int) option =
  match lp.preheader, lp.latches with
  | Some preheader, [ latch ] ->
      let header = lp.header in
      let header_bb = IntMap.find header bmap in
      let header_phis, header_rest = U.partition_header_instrs header_bb in
      let is_self_loop = header = latch in
      let body_bb = if is_self_loop then None else Some (IntMap.find latch bmap) in
      let body_instrs =
        if is_self_loop then header_rest
        else (Option.get body_bb).bb_instrs
      in
      if List.exists (function Alloca _ | Phi _ -> true | _ -> false) body_instrs then None
      else if (not is_self_loop)
              && (match body_bb with
                  | Some bb -> bb.bb_term <> Jump header
                  | None -> true)
      then None
      else begin
        let body_defs = build_body_defs body_instrs in
        let basic_ivs = detect_basic_ivs header_phis preheader latch body_defs in
        let basic_iv_set =
          IntSet.of_list (List.map (fun (b : basic_iv) -> b.iv) basic_ivs)
        in

        let raw_candidates =
          List.filter_map (fun instr ->
            match instr with
            | Binop { dst; _ } ->
                (match affine_of_value body_defs basic_iv_set (VReg dst) with
                 | Some aff when aff.a <> 0 && abs aff.a > 1 -> Some (dst, aff)
                 | _ -> None)
            | _ -> None
          ) body_instrs
        in

        if raw_candidates = [] then None
        else begin
          let next_vreg = ref (f.f_max_vreg + 1) in
          let fresh_vreg () = let x = !next_vreg in incr next_vreg; x in
          let pre_instrs = ref [] in
          let new_phis = ref [] in
          let inc_instrs = ref [] in
          let phi_map = ref IntMap.empty in

          List.iter (fun (dst, aff) ->
            match aff.iv with
            | None -> ()
            | Some iv ->
                match List.find_opt (fun (b : basic_iv) -> b.iv = iv) basic_ivs with
                | None -> ()
                | Some basic ->
                    let a = aff.a and b = aff.b in
                    let delta = a * basic.step in
                    let phi_dst = fresh_vreg () in
                    let next_dst = fresh_vreg () in
                    let init_val =
                      emit_affine_init fresh_vreg pre_instrs basic.init a b in
                    new_phis := Phi { dst = phi_dst;
                                      incoming = [ (init_val, preheader);
                                                   (VReg next_dst, latch) ] }
                               :: !new_phis;
                    let inc =
                      if delta >= 0 then
                        Binop { dst = next_dst; op = Add;
                                lhs = VReg phi_dst; rhs = Imm delta }
                      else
                        Binop { dst = next_dst; op = Sub;
                                lhs = VReg phi_dst; rhs = Imm (-delta) }
                    in
                    inc_instrs := inc :: !inc_instrs;
                    phi_map := IntMap.add dst phi_dst !phi_map
          ) raw_candidates;

          let replaced_body_instrs =
            List.map (fun instr ->
              match instr_dst instr with
              | Some dst when IntMap.mem dst !phi_map ->
                  Copy { dst; src = VReg (IntMap.find dst !phi_map) }
              | _ -> instr
            ) body_instrs
          in
          let final_body_instrs = replaced_body_instrs @ List.rev !inc_instrs in

          let new_header =
            if is_self_loop then
              { header_bb with
                bb_instrs = header_phis @ List.rev !new_phis @ final_body_instrs }
            else
              { header_bb with
                bb_instrs = header_phis @ List.rev !new_phis @ header_rest }
          in
          let bmap = IntMap.add header new_header bmap in

          let bmap =
            if is_self_loop then bmap
            else
              let body_bb = Option.get body_bb in
              IntMap.add latch { body_bb with bb_instrs = final_body_instrs } bmap
          in

          let preheader_bb = IntMap.find preheader bmap in
          let new_preheader =
            { preheader_bb with
              bb_instrs = preheader_bb.bb_instrs @ List.rev !pre_instrs }
          in
          let bmap = IntMap.add preheader new_preheader bmap in
          Some (bmap, !next_vreg - 1)
        end
      end
  | _ -> None

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
