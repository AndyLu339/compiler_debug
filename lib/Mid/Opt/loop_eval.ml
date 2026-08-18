(* ToyC 优化 — 循环求值 / 归纳变量求值
   复用 canonical counted loop 识别, 对无副作用且可静态求值的循环体做编译期迭代计算。
   当前支持:
   - 精确 trip count 的 canonical loop（要求唯一 header exit）
   - preheader / loop 内仅含纯整数 SSA 指令
   - 通过 phi 表示的归纳变量与归约变量 *)

open Ir_types
open Common
open Loop_info

module IntMap = Map.Make (Int)
module U = Loop_unroll

let max_evaluated_trip_count = 10000

type sym_expr = {
  const : int;
  terms : int IntMap.t;  (* 外部 SSA vreg -> 系数 *)
}

let expr_const n = { const = n; terms = IntMap.empty }
let expr_symbol r = { const = 0; terms = IntMap.singleton r 1 }

let normalize_expr (e : sym_expr) =
  { e with terms = IntMap.filter (fun _ coeff -> coeff <> 0) e.terms }

let add_term coeff key terms =
  let prev = Option.value ~default:0 (IntMap.find_opt key terms) in
  let next = prev + coeff in
  if next = 0 then IntMap.remove key terms else IntMap.add key next terms

let add_expr (lhs : sym_expr) (rhs : sym_expr) =
  normalize_expr
    {
      const = lhs.const + rhs.const;
      terms =
        IntMap.fold (fun key coeff acc -> add_term coeff key acc) rhs.terms lhs.terms;
    }

let sub_expr (lhs : sym_expr) (rhs : sym_expr) =
  normalize_expr
    {
      const = lhs.const - rhs.const;
      terms =
        IntMap.fold (fun key coeff acc -> add_term (-coeff) key acc) rhs.terms lhs.terms;
    }

let scale_expr k (e : sym_expr) =
  normalize_expr
    {
      const = k * e.const;
      terms = IntMap.map (fun coeff -> k * coeff) e.terms;
    }

let const_of_expr (e : sym_expr) =
  if IntMap.is_empty e.terms then Some e.const else None

let eval_binop (op : binary_op) (l : int) (r : int) : int =
  let l = wrap32 l and r = wrap32 r in
  match op with
  | Add -> wrap32 (l + r)
  | Sub -> wrap32 (l - r)
  | Mul -> wrap32 (l * r)
  | Div -> wrap32 (l / r)
  | Mod -> wrap32 (l mod r)
  | Eq  -> if l = r then 1 else 0
  | Ne  -> if l <> r then 1 else 0
  | Lt  -> if l < r then 1 else 0
  | Gt  -> if l > r then 1 else 0
  | Le  -> if l <= r then 1 else 0
  | Ge  -> if l >= r then 1 else 0
  | LAnd | LOr -> failwith "LAnd/LOr should be lowered before IR"

let eval_icmp (cond : icmp_cond) (l : int) (r : int) : int =
  let l = wrap32 l and r = wrap32 r in
  match cond with
  | IEq  -> if l = r then 1 else 0
  | INe  -> if l <> r then 1 else 0
  | ISlt -> if l < r then 1 else 0
  | ISle -> if l <= r then 1 else 0
  | ISgt -> if l > r then 1 else 0
  | ISge -> if l >= r then 1 else 0

let eval_value (env : sym_expr IntMap.t) = function
  | Imm n -> Some (expr_const n)
  | VReg r ->
      begin match IntMap.find_opt r env with
      | Some e -> Some e
      | None -> Some (expr_symbol r)
      end
  | Global _ -> None

let eval_instr (env : sym_expr IntMap.t) = function
  | Binop { dst; op; lhs; rhs } ->
      begin match eval_value env lhs, eval_value env rhs with
      | Some l, Some r ->
          let result =
            match op with
            | Add -> Some (add_expr l r)
            | Sub -> Some (sub_expr l r)
            | Mul ->
                begin match const_of_expr l, const_of_expr r with
                | Some c, None -> Some (scale_expr c r)
                | None, Some c -> Some (scale_expr c l)
                | Some lc, Some rc -> Some (expr_const (eval_binop op lc rc))
                | None, None -> None
                end
            | Div | Mod | Eq | Ne | Lt | Gt | Le | Ge ->
                begin match const_of_expr l, const_of_expr r with
                | Some lc, Some rc -> Some (expr_const (eval_binop op lc rc))
                | _ -> None
                end
            | LAnd | LOr ->
                None
          in
          begin match result with
          | Some e -> Some (IntMap.add dst e env)
          | None -> None
          end
      | _ ->
          None
      end
  | Icmp { dst; cond; lhs; rhs } ->
      begin match eval_value env lhs, eval_value env rhs with
      | Some l, Some r ->
          begin match const_of_expr l, const_of_expr r with
          | Some lc, Some rc ->
              Some (IntMap.add dst (expr_const (eval_icmp cond lc rc)) env)
          | _ ->
              None
          end
      | _ ->
          None
      end
  | Zext { dst; src } ->
      begin match eval_value env src with
      | Some v ->
          begin match const_of_expr v with
          | Some n ->
              Some (IntMap.add dst (expr_const (if n <> 0 then 1 else 0)) env)
          | None ->
              None
          end
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
  | Shl { dst; lhs; rhs } ->
      begin match eval_value env lhs, eval_value env rhs with
      | Some l, Some r ->
          begin match const_of_expr r with
          | Some k when k >= 0 ->
              Some (IntMap.add dst (scale_expr (1 lsl k) l) env)
          | _ ->
              None
          end
      | _ ->
          None
      end
  | AShr { dst; lhs; rhs } ->
      begin match eval_value env lhs, eval_value env rhs with
      | Some l, Some r ->
          begin match const_of_expr l, const_of_expr r with
          | Some lc, Some rc ->
              Some (IntMap.add dst (expr_const (lc asr rc)) env)
          | _ ->
              None
          end
      | _ ->
          None
      end
  | And { dst; lhs; rhs } ->
      begin match eval_value env lhs, eval_value env rhs with
      | Some l, Some r ->
          begin match const_of_expr l, const_of_expr r with
          | Some lc, Some rc ->
              Some (IntMap.add dst (expr_const (lc land rc)) env)
          | _ ->
              None
          end
      | _ ->
          None
      end
  | Alloca _ | Load _ | Store _ | Call _ | Phi _ ->
      None

let eval_instrs (env : sym_expr IntMap.t) (instrs : instr list) =
  List.fold_left (fun acc instr ->
    match acc with
    | None -> None
    | Some env -> eval_instr env instr
  ) (Some env) instrs

let eval_term (env : sym_expr IntMap.t) = function
  | Ret None
  | Jump _ ->
      Some env
  | Ret (Some v)
  | Br (v, _, _) ->
      begin match eval_value env v with
      | Some cond ->
          begin match const_of_expr cond with
          | Some _ -> Some env
          | None -> None
          end
      | None ->
          None
      end

let eval_block env (bb : basic_block) =
  match eval_instrs env bb.bb_instrs with
  | None -> None
  | Some env' -> eval_term env' bb.bb_term

let init_loop_state (pre_env : sym_expr IntMap.t) (phis : U.phi_info list) =
  List.fold_left (fun acc (phi : U.phi_info) ->
    match acc, eval_value pre_env phi.init with
    | Some m, Some e -> Some (IntMap.add phi.dst e m)
    | _ -> None
  ) (Some IntMap.empty) phis

let phi_value_for_latch (phi : U.phi_info) (latch : label) =
  List.find_map (fun (pred, v) -> if pred = latch then Some v else None) phi.latch_incomings

let step_loop_state
    (bmap : basic_block U.IntMap.t)
    (spec : U.counted_loop)
    (curr : sym_expr IntMap.t)
  =
  let header_bb = U.IntMap.find spec.header bmap in
  let _, header_rest = U.partition_header_instrs header_bb in
  let rec exec visited env lbl =
    if U.IntSet.mem lbl visited then
      None
    else
      let bb = U.IntMap.find lbl bmap in
      match eval_instrs env bb.bb_instrs with
      | None ->
          None
      | Some env' ->
          let continue_to succ =
            if succ = spec.header then
              List.fold_left (fun acc (phi : U.phi_info) ->
                match acc, phi_value_for_latch phi lbl with
                | Some m, Some latch_v ->
                    begin match eval_value env' latch_v with
                    | Some e -> Some (IntMap.add phi.dst e m)
                    | None -> None
                    end
                | _ ->
                    None
              ) (Some IntMap.empty) spec.phis
            else if U.IntSet.mem succ spec.blocks then
              exec (U.IntSet.add lbl visited) env' succ
            else
              None
          in
          begin match bb.bb_term with
          | Jump succ ->
              continue_to succ
          | Br (cond, t_lbl, f_lbl) ->
              begin match eval_value env' cond with
              | Some cond_e ->
                  begin match const_of_expr cond_e with
                  | Some 0 -> continue_to f_lbl
                  | Some _ -> continue_to t_lbl
                  | None -> None
                  end
              | None ->
                  None
              end
          | Ret _ ->
              None
          end
  in
  match eval_instrs curr header_rest with
  | None -> None
  | Some env -> exec U.IntSet.empty env spec.body_entry

let rec iterate_loop bmap spec fuel curr =
  if fuel = 0 then
    Some curr
  else
    match step_loop_state bmap spec curr with
    | None -> None
    | Some next -> iterate_loop bmap spec (fuel - 1) next

let compute_final_env (header_bb : basic_block) (final_phi_state : sym_expr IntMap.t) =
  let _, header_rest = U.partition_header_instrs header_bb in
  match eval_instrs final_phi_state header_rest with
  | Some env -> env
  | None -> final_phi_state

let detect_counted_loop (bmap : basic_block U.IntMap.t) (lp : loop) =
  match U.detect_counted_loop bmap lp with
  | None ->
      None
  | Some spec ->
      let pure_block lbl =
        let bb = U.IntMap.find lbl bmap in
        let instrs =
          if lbl = spec.header then snd (U.partition_header_instrs bb) else bb.bb_instrs
        in
        List.for_all (function
          | Alloca _ | Load _ | Store _ | Call _ | Phi _ -> false
          | _ -> true
        ) instrs
      in
      if U.IntSet.for_all pure_block spec.blocks then Some spec else None

let remove_evaluated_loop
    (f : func)
    (bmap : basic_block U.IntMap.t)
    (spec : U.counted_loop)
    (final_env : sym_expr IntMap.t)
  =
  let next_vreg = ref (f.f_max_vreg + 1) in
  let fresh_vreg () = let r = !next_vreg in incr next_vreg; r in

  let emit_expr (e : sym_expr) =
    let emitted = ref [] in
    let emit i = emitted := i :: !emitted in
    let make_mul coeff base =
      if coeff = 1 then base
      else if coeff = -1 then begin
        let dst = fresh_vreg () in
        emit (Binop { dst; op = Sub; lhs = Imm 0; rhs = base });
        VReg dst
      end else begin
        let mag = abs coeff in
        let mul_dst = fresh_vreg () in
        emit (Binop { dst = mul_dst; op = Mul; lhs = base; rhs = Imm mag });
        if coeff > 0 then
          VReg mul_dst
        else begin
          let neg_dst = fresh_vreg () in
          emit (Binop { dst = neg_dst; op = Sub; lhs = Imm 0; rhs = VReg mul_dst });
          VReg neg_dst
        end
      end
    in
    let add_value acc value =
      match acc with
      | None -> Some value
      | Some lhs ->
          let dst = fresh_vreg () in
          emit (Binop { dst; op = Add; lhs; rhs = value });
          Some (VReg dst)
    in
    let acc =
      IntMap.bindings e.terms
      |> List.fold_left (fun acc (sym, coeff) ->
        add_value acc (make_mul coeff (VReg sym))
      ) (if e.const = 0 then None else Some (Imm e.const))
    in
    (List.rev !emitted, Option.value ~default:(Imm 0) acc)
  in

  let materialized =
    IntMap.fold (fun r expr (instrs_acc, value_acc) ->
      let instrs, value =
        match const_of_expr expr with
        | Some n -> ([], Imm n)
        | None ->
            begin match IntMap.bindings expr.terms with
            | [ (sym, 1) ] when expr.const = 0 -> ([], VReg sym)
            | _ -> emit_expr expr
            end
      in
      (instrs_acc @ instrs, IntMap.add r value value_acc)
    ) final_env ([], IntMap.empty)
  in
  let preheader_extra, value_map = materialized in
  let resolve r = IntMap.find_opt r value_map in
  let remaining =
    U.IntMap.filter (fun lbl _ ->
      not (U.IntSet.mem lbl spec.blocks)
    ) bmap
    |> U.IntMap.map (fun bb ->
        let bb =
          { bb with
            bb_instrs = List.map (U.map_instr_values resolve) bb.bb_instrs;
            bb_term = U.map_term_values resolve bb.bb_term
          }
        in
        if bb.bb_label = spec.preheader then
          {
            bb with
            bb_instrs = bb.bb_instrs @ preheader_extra;
            bb_term = U.rewrite_succ spec.header spec.exit_block bb.bb_term;
          }
        else if bb.bb_label = spec.exit_block then
          let fix_instr = function
            | Phi p ->
                let incoming =
                  List.filter_map (fun (v, lbl) ->
                    if U.IntSet.mem lbl spec.blocks then
                      if lbl = spec.header then
                        Some (U.map_value resolve v, spec.preheader)
                      else
                        None
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
    f_max_vreg = !next_vreg - 1;
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
        match eval_block IntMap.empty preheader_bb with
        | None ->
          None
        | Some pre_env ->
            begin match init_loop_state pre_env spec.phis with
            | None ->
                None
            | Some init_state ->
                begin match iterate_loop bmap spec spec.trip_count init_state with
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
