(* ToyC 优化 — 循环求值 / 归纳变量求值
   复用 canonical counted loop 识别, 对无副作用且可静态求值的循环体做编译期迭代计算。
   当前支持:
   - 精确 trip count 的两块循环 (header + body)
   - preheader / body 中仅含纯整数 SSA 指令
   - 通过 phi 表示的归纳变量与归约变量 *)

open Ir_types
open Common
open Loop_info

module IntMap = Map.Make (Int)
module U = Loop_unroll

let max_evaluated_trip_count = 10000

let eval_binop (op : binary_op) (l : int) (r : int) : int =
  match op with
  | Add -> l + r
  | Sub -> l - r
  | Mul -> l * r
  | Div -> l / r
  | Mod -> l mod r
  | Eq  -> if l = r then 1 else 0
  | Ne  -> if l <> r then 1 else 0
  | Lt  -> if l < r then 1 else 0
  | Gt  -> if l > r then 1 else 0
  | Le  -> if l <= r then 1 else 0
  | Ge  -> if l >= r then 1 else 0
  | LAnd | LOr -> failwith "LAnd/LOr should be lowered before IR"

let eval_icmp (cond : icmp_cond) (l : int) (r : int) : int =
  match cond with
  | IEq  -> if l = r then 1 else 0
  | INe  -> if l <> r then 1 else 0
  | ISlt -> if l < r then 1 else 0
  | ISle -> if l <= r then 1 else 0
  | ISgt -> if l > r then 1 else 0
  | ISge -> if l >= r then 1 else 0

let eval_value (env : int IntMap.t) = function
  | Imm n -> Some n
  | VReg r -> IntMap.find_opt r env
  | Global _ -> None

let eval_instr (env : int IntMap.t) = function
  | Binop { dst; op; lhs; rhs } ->
      begin match eval_value env lhs, eval_value env rhs with
      | Some l, Some r ->
          Some (IntMap.add dst (eval_binop op l r) env)
      | _ ->
          None
      end
  | Icmp { dst; cond; lhs; rhs } ->
      begin match eval_value env lhs, eval_value env rhs with
      | Some l, Some r ->
          Some (IntMap.add dst (eval_icmp cond l r) env)
      | _ ->
          None
      end
  | Zext { dst; src } ->
      begin match eval_value env src with
      | Some v ->
          Some (IntMap.add dst (if v <> 0 then 1 else 0) env)
      | None ->
          None
      end
  | Copy { dst; src } ->
      begin match eval_value env src with
      | Some v ->
          Some (IntMap.add dst v env)
      | None ->
          None
      end
  | Shl _ | AShr _ | And _ | Alloca _ | Load _ | Store _ | Call _ | Phi _ ->
      None

let eval_instrs (env : int IntMap.t) (instrs : instr list) =
  List.fold_left (fun acc instr ->
    match acc with
    | None -> None
    | Some env -> eval_instr env instr
  ) (Some env) instrs

let eval_term (env : int IntMap.t) = function
  | Ret None
  | Jump _ ->
      Some env
  | Ret (Some v)
  | Br (v, _, _) ->
      begin match eval_value env v with
      | Some _ -> Some env
      | None -> None
      end

let eval_block env (bb : basic_block) =
  match eval_instrs env bb.bb_instrs with
  | None -> None
  | Some env' -> eval_term env' bb.bb_term

let init_loop_state (pre_env : int IntMap.t) (phis : (int * value * value) list) =
  List.fold_left (fun acc (dst, init, _) ->
    match acc, eval_value pre_env init with
    | Some m, Some n -> Some (IntMap.add dst n m)
    | _ -> None
  ) (Some IntMap.empty) phis

let step_loop_state (body_bb : basic_block) (phis : (int * value * value) list) (curr : int IntMap.t) =
  match eval_block curr body_bb with
  | None ->
      None
  | Some env ->
      List.fold_left (fun acc (dst, _, latch_v) ->
        match acc, eval_value env latch_v with
        | Some m, Some n -> Some (IntMap.add dst n m)
        | _ -> None
      ) (Some IntMap.empty) phis

let rec iterate_loop body_bb phis fuel curr =
  if fuel = 0 then
    Some curr
  else
    match step_loop_state body_bb phis curr with
    | None -> None
    | Some next -> iterate_loop body_bb phis (fuel - 1) next

let compute_final_env (header_bb : basic_block) (final_phi_state : int IntMap.t) =
  let _, header_rest = U.partition_header_instrs header_bb in
  match eval_instrs final_phi_state header_rest with
  | Some env -> env
  | None -> final_phi_state

let detect_counted_loop (bmap : basic_block U.IntMap.t) (lp : loop) =
  try
    if U.IntSet.cardinal lp.blocks <> 2 then None else
    match lp.preheader, lp.latches with
    | Some preheader, [ body ] ->
        let header_bb = U.IntMap.find lp.header bmap in
        let body_bb = U.IntMap.find body bmap in
        if List.exists (function Alloca _ | Phi _ -> true | _ -> false) body_bb.bb_instrs
        then raise Exit;
        begin match body_bb.bb_term with
        | Jump lbl when lbl = lp.header -> ()
        | _ -> raise Exit
        end;
        begin match header_bb.bb_term with
        | Br (cond_v, t_lbl, f_lbl) ->
            let body_on_true, exit_block =
              if t_lbl = body && f_lbl <> body then (true, f_lbl)
              else if f_lbl = body && t_lbl <> body then (false, t_lbl)
              else raise Exit
            in
            let header_phis, header_rest = U.partition_header_instrs header_bb in
            let header_defs =
              List.fold_left (fun defs instr ->
                match instr_dst instr with
                | Some dst -> U.IntMap.add dst instr defs
                | None -> defs
              ) U.IntMap.empty header_rest
            in
            let (cmp_cond, lhs, rhs, negated) =
              match U.extract_compare header_defs cond_v with
              | Some info -> info
              | None -> raise Exit
            in
            let continue_cond =
              let cond = if negated then U.negate_cond cmp_cond else cmp_cond in
              if body_on_true then cond else U.negate_cond cond
            in
            let iv, continue_cond, bound =
              match U.canonicalize_cmp continue_cond lhs rhs with
              | Some info -> info
              | None -> raise Exit
            in
            let body_defs =
              List.fold_left (fun defs instr ->
                match instr_dst instr with
                | Some dst -> U.IntMap.add dst instr defs
                | None -> defs
              ) U.IntMap.empty body_bb.bb_instrs
            in
            let phis =
              List.map (function
                | Phi { dst; incoming } ->
                    let init =
                      match U.find_incoming preheader incoming with
                      | Some v -> v
                      | None -> raise Exit
                    in
                    let latch =
                      match U.find_incoming body incoming with
                      | Some v -> v
                      | None -> raise Exit
                    in
                    (dst, init, latch)
                | _ -> raise Exit
              ) header_phis
            in
            let trip_count =
              match List.find_opt (fun (dst, _, _) -> dst = iv) phis with
              | Some (_, Imm init, latch_v) ->
                  let step =
                    match U.extract_step body_defs iv latch_v with
                    | Some s when s <> 0 -> s
                    | _ -> raise Exit
                  in
                  begin match U.compute_trip_count init step continue_cond bound with
                  | Some n -> n
                  | None -> raise Exit
                  end
              | _ ->
                  raise Exit
            in
            Some { U.header = lp.header; preheader; body; exit_block; trip_count; phis }
        | _ ->
            None
        end
    | _ ->
        None
  with Exit ->
    None

let remove_evaluated_loop
    (f : func)
    (bmap : basic_block U.IntMap.t)
    (spec : U.counted_loop)
    (final_env : int IntMap.t)
  =
  let resolve r =
    Option.map (fun n -> Imm n) (IntMap.find_opt r final_env)
  in
  let remaining =
    U.IntMap.filter (fun lbl _ ->
      lbl <> spec.header && lbl <> spec.body
    ) bmap
    |> U.IntMap.map (fun bb ->
      let bb =
        { bb with
          bb_instrs = List.map (U.map_instr_values resolve) bb.bb_instrs;
          bb_term = U.map_term_values resolve bb.bb_term
        }
      in
      if bb.bb_label = spec.preheader then
        { bb with bb_term = U.rewrite_succ spec.header spec.exit_block bb.bb_term }
      else if bb.bb_label = spec.exit_block then
        let fix_instr = function
          | Phi p ->
              let incoming =
                List.filter_map (fun (v, lbl) ->
                  if lbl = spec.body then
                    None
                  else if lbl = spec.header then
                    Some (U.map_value resolve v, spec.preheader)
                  else
                    Some (U.map_value resolve v, lbl)
                ) p.incoming
              in
              Phi { p with incoming }
          | i -> i
        in
        { bb with bb_instrs = List.map fix_instr bb.bb_instrs }
      else
        bb
    )
  in
  { f with
    f_blocks =
      U.IntMap.bindings remaining
      |> List.sort (fun (a, _) (b, _) -> compare a b)
  }

let run_on_func (f : func) : func =
  let rec fixpoint (f : func) =
    let bmap = U.build_bmap f in
    let dom = Dominance.analyze f in
    let li = Loop_info.analyze f dom in
    let loops =
      List.sort (fun a b ->
        let c = compare b.depth a.depth in
        if c <> 0 then c else compare a.header b.header
      ) li.loops
    in
    let evaluate_loop (spec : U.counted_loop) =
      if spec.trip_count > max_evaluated_trip_count then
        None
      else
        let header_bb = U.IntMap.find spec.header bmap in
        let preheader_bb = U.IntMap.find spec.preheader bmap in
        let body_bb = U.IntMap.find spec.body bmap in
        match eval_block IntMap.empty preheader_bb with
        | None ->
            None
        | Some pre_env ->
            begin match init_loop_state pre_env spec.phis with
            | None ->
                None
            | Some init_state ->
                begin match iterate_loop body_bb spec.phis spec.trip_count init_state with
                | None ->
                    None
                | Some final_state ->
                    Some (compute_final_env header_bb final_state)
                end
            end
    in
    match List.find_map (fun lp ->
      match detect_counted_loop bmap lp with
      | None -> None
      | Some spec ->
          Option.map (fun final_env -> (spec, final_env)) (evaluate_loop spec)
    ) loops with
    | None ->
        f
    | Some (spec, final_env) ->
        fixpoint (remove_evaluated_loop f bmap spec final_env)
  in
  fixpoint f

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
