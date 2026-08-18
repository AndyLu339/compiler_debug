(* ToyC 优化 — 循环展开
    参考 LLVM：counted loop 的识别基于 preheader/header/latch/exit 的规范形，
   而不是把“只有两个块”当成 counted loop 的定义。
   本文件把 counted loop 的公共识别与 loop-unroll 自身可处理的简化子集分开：
   - detect_counted_loop: 识别一般的 canonical counted loop
   - detect_simple_unroll_loop: 只接受当前完全展开器真正能处理的两块子集 *)

open Ir_types
open Common
open Loop_info

module IntSet = Set.Make (Int)
module IntMap = Map.Make (Int)

let max_full_unroll_count = 16
let max_unrolled_instrs = 64

type counted_loop = {
  header       : label;
  preheader    : label;
  body_entry   : label;
  exit_block   : label;
  trip_count   : int;
  iv           : int;
  step         : int;
  latches      : label list;
  blocks       : IntSet.t;
  phis         : phi_info list;
}

and phi_info = {
  dst             : int;
  init            : value;
  latch_incomings : (label * value) list;
}

type simple_unroll_loop = {
  counted : counted_loop;
  body    : label;
}

let build_bmap (f : func) =
  List.fold_left (fun m (lbl, bb) -> IntMap.add lbl bb m) IntMap.empty f.f_blocks

let unique_labels labels =
  labels
  |> List.fold_left (fun seen lbl -> IntSet.add lbl seen) IntSet.empty
  |> IntSet.elements

let map_value (f : int -> value option) (v : value) =
  match v with
  | Imm _ | Global _ -> v
  | VReg r -> Option.value ~default:v (f r)

let map_instr_values (f : int -> value option) = function
  | Alloca _ as i -> i
  | Load l -> Load { l with ptr = map_value f l.ptr }
  | Store s -> Store { val_ = map_value f s.val_; ptr = map_value f s.ptr }
  | Binop b -> Binop { b with lhs = map_value f b.lhs; rhs = map_value f b.rhs }
  | Icmp c -> Icmp { c with lhs = map_value f c.lhs; rhs = map_value f c.rhs }
  | Call c -> Call { c with args = List.map (map_value f) c.args }
  | Phi p ->
      Phi {
        p with
        incoming = List.map (fun (v, lbl) -> (map_value f v, lbl)) p.incoming;
      }
  | Shl s -> Shl { s with lhs = map_value f s.lhs; rhs = map_value f s.rhs }
  | AShr s -> AShr { s with lhs = map_value f s.lhs; rhs = map_value f s.rhs }
  | And a -> And { a with lhs = map_value f a.lhs; rhs = map_value f a.rhs }
  | Zext z -> Zext { z with src = map_value f z.src }
  | Copy c -> Copy { c with src = map_value f c.src }

let map_term_values (f : int -> value option) = function
  | Ret (Some v) -> Ret (Some (map_value f v))
  | Ret None as t -> t
  | Br (cond, t, fl) -> Br (map_value f cond, t, fl)
  | Jump _ as t -> t

let rewrite_succ old_lbl new_lbl = function
  | Jump lbl when lbl = old_lbl -> Jump new_lbl
  | Br (cond, t, f) ->
      let t = if t = old_lbl then new_lbl else t in
      let f = if f = old_lbl then new_lbl else f in
      Br (cond, t, f)
  | t -> t

let swap_cond = function
  | ISlt -> ISgt
  | ISle -> ISge
  | ISgt -> ISlt
  | ISge -> ISle
  | IEq -> IEq
  | INe -> INe

let negate_cond = function
  | IEq -> INe
  | INe -> IEq
  | ISlt -> ISge
  | ISle -> ISgt
  | ISgt -> ISle
  | ISge -> ISlt

let int64_ceil_div_pos n d =
  Int64.(to_int (div (add n (sub d 1L)) d))

let compute_trip_count init step cond bound =
  let init = Int64.of_int init in
  let step = Int64.of_int step in
  let bound = Int64.of_int bound in
  match cond with
  | ISlt when step > 0L ->
      if init >= bound then Some 0
      else Some (int64_ceil_div_pos Int64.(sub bound init) step)
  | ISle when step > 0L ->
      if init > bound then Some 0
      else Some Int64.(to_int (add (div (sub bound init) step) 1L))
  | ISgt when step < 0L ->
      let step = Int64.neg step in
      if init <= bound then Some 0
      else Some (int64_ceil_div_pos Int64.(sub init bound) step)
  | ISge when step < 0L ->
      let step = Int64.neg step in
      if init < bound then Some 0
      else Some Int64.(to_int (add (div (sub init bound) step) 1L))
  | _ ->
      None

let partition_header_instrs (bb : basic_block) =
  let rec take_phis acc = function
    | Phi _ as i :: tl -> take_phis (i :: acc) tl
    | rest -> (List.rev acc, rest)
  in
  take_phis [] bb.bb_instrs

let find_incoming lbl incoming =
  List.find_map (fun (v, pred) -> if pred = lbl then Some v else None) incoming

let find_latch_value lbl incoming =
  List.find_map (fun (pred, v) -> if pred = lbl then Some v else None) incoming

let rec extract_compare defs (v : value) =
  match v with
  | Imm _ | Global _ -> None
  | VReg r ->
      match IntMap.find_opt r defs with
      | Some (Copy { src; _ }) -> extract_compare defs src
      | Some (Zext { src; _ }) -> extract_compare defs src
      | Some (Icmp { cond = INe; lhs; rhs; _ }) ->
          begin match lhs, rhs with
          | Imm 0, other | other, Imm 0 ->
              Option.map (fun (cond, lhs, rhs, neg) -> (cond, lhs, rhs, neg))
                (extract_compare defs other)
          | _ ->
              None
          end
      | Some (Icmp { cond = IEq; lhs; rhs; _ }) ->
          begin match lhs, rhs with
          | Imm 0, other | other, Imm 0 ->
              Option.map (fun (cond, lhs, rhs, neg) -> (cond, lhs, rhs, not neg))
                (extract_compare defs other)
          | _ ->
              None
          end
      | Some (Icmp { cond; lhs; rhs; _ }) ->
          Some (cond, lhs, rhs, false)
      | _ ->
          None

let canonicalize_cmp cond lhs rhs =
  match lhs, rhs with
  | VReg iv, Imm bound -> Some (iv, cond, bound)
  | Imm bound, VReg iv -> Some (iv, swap_cond cond, bound)
  | _ -> None

let rec extract_step body_defs iv = function
  | Imm _ | Global _ -> None
  | VReg r when r = iv -> Some 0
  | VReg r ->
      match IntMap.find_opt r body_defs with
      | Some (Copy { src; _ }) ->
          extract_step body_defs iv src
      | Some (Binop { op = Add; lhs = VReg x; rhs = Imm k; _ }) when x = iv ->
          Some k
      | Some (Binop { op = Add; lhs = Imm k; rhs = VReg x; _ }) when x = iv ->
          Some k
      | Some (Binop { op = Sub; lhs = VReg x; rhs = Imm k; _ }) when x = iv ->
          Some (-k)
      | _ ->
          None

let build_defs_of_instrs instrs =
  List.fold_left (fun defs instr ->
    match instr_dst instr with
    | Some dst -> IntMap.add dst instr defs
    | None -> defs
  ) IntMap.empty instrs

let build_loop_defs (bmap : basic_block IntMap.t) (lp : loop) =
  IntSet.fold (fun lbl defs ->
    let bb = IntMap.find lbl bmap in
    let instrs =
      if lbl = lp.header then
        snd (partition_header_instrs bb)
      else
        bb.bb_instrs
    in
    List.fold_left (fun defs instr ->
      match instr_dst instr with
      | Some dst -> IntMap.add dst instr defs
      | None -> defs
    ) defs instrs
  ) lp.blocks IntMap.empty

let detect_counted_loop (bmap : basic_block IntMap.t) (lp : loop) =
  try
    match lp.preheader, unique_labels lp.latches with
    | Some preheader, latches when latches <> [] ->
        let header_bb = IntMap.find lp.header bmap in
        begin match header_bb.bb_term with
        | Br (cond_v, t_lbl, f_lbl) ->
            let t_in_loop = IntSet.mem t_lbl lp.blocks in
            let f_in_loop = IntSet.mem f_lbl lp.blocks in
            let body_on_true, body_entry, exit_block =
              if t_in_loop && not f_in_loop then (true, t_lbl, f_lbl)
              else if f_in_loop && not t_in_loop then (false, f_lbl, t_lbl)
              else raise Exit
            in
            let exiting = unique_labels lp.exiting in
            if exiting <> [ lp.header ] then raise Exit;
            let header_phis, header_rest = partition_header_instrs header_bb in
            let header_defs = build_defs_of_instrs header_rest in
            let (cmp_cond, lhs, rhs, negated) =
              match extract_compare header_defs cond_v with
              | Some info -> info
              | None -> raise Exit
            in
            let continue_cond =
              let cond = if negated then negate_cond cmp_cond else cmp_cond in
              if body_on_true then cond else negate_cond cond
            in
            let iv, continue_cond, bound =
              match canonicalize_cmp continue_cond lhs rhs with
              | Some info -> info
              | None -> raise Exit
            in
            let loop_defs = build_loop_defs bmap lp in
            let phis =
              List.map (function
                | Phi { dst; incoming } ->
                    let init =
                      match find_incoming preheader incoming with
                      | Some v -> v
                      | None -> raise Exit
                    in
                    let latch_incomings =
                      List.map (fun latch ->
                        match find_incoming latch incoming with
                        | Some v -> (latch, v)
                        | None -> raise Exit
                      ) latches
                    in
                    { dst; init; latch_incomings }
                | _ -> raise Exit
              ) header_phis
            in
            let iv_phi =
              match List.find_opt (fun phi -> phi.dst = iv) phis with
              | Some phi -> phi
              | None -> raise Exit
            in
            let init, step =
              match iv_phi.init with
              | Imm init ->
                  let steps =
                    List.map (fun (_, latch_v) ->
                      match extract_step loop_defs iv latch_v with
                      | Some s when s <> 0 -> s
                      | _ -> raise Exit
                    ) iv_phi.latch_incomings
                  in
                  begin match steps with
                  | [] -> raise Exit
                  | step :: rest when List.for_all (( = ) step) rest -> (init, step)
                  | _ -> raise Exit
                  end
              | _ ->
                  raise Exit
            in
            let trip_count =
              match compute_trip_count init step continue_cond bound with
              | Some n -> n
              | None -> raise Exit
            in
            Some {
              header = lp.header;
              preheader;
              body_entry;
              exit_block;
              trip_count;
              iv;
              step;
              latches;
              blocks = lp.blocks;
              phis;
            }
        | _ ->
            None
        end
    | _ ->
        None
  with Exit ->
    None

let detect_simple_unroll_loop (bmap : basic_block IntMap.t) (spec : counted_loop) =
  try
    let body_blocks =
      IntSet.remove spec.header spec.blocks
      |> IntSet.elements
    in
    match spec.latches, body_blocks with
    | [ body ], [ body' ] when body = body' && body = spec.body_entry ->
        let body_bb = IntMap.find body bmap in
        if List.exists (function Alloca _ | Phi _ -> true | _ -> false) body_bb.bb_instrs
        then raise Exit;
        begin match body_bb.bb_term with
        | Jump lbl when lbl = spec.header -> ()
        | _ -> raise Exit
        end;
        if spec.trip_count > max_full_unroll_count then raise Exit;
        if spec.trip_count * List.length body_bb.bb_instrs > max_unrolled_instrs
        then raise Exit;
        Some { counted = spec; body }
    | _ ->
        None
  with Exit ->
    None

let clone_instr fresh remap = function
  | Alloca _ -> raise Exit
  | Load { dst; ptr } ->
      let dst' = fresh () in
      (Load { dst = dst'; ptr = remap ptr }, (dst, dst'))
  | Store { val_; ptr } ->
      (Store { val_ = remap val_; ptr = remap ptr }, (-1, -1))
  | Binop { dst; op; lhs; rhs } ->
      let dst' = fresh () in
      (Binop { dst = dst'; op; lhs = remap lhs; rhs = remap rhs }, (dst, dst'))
  | Icmp { dst; cond; lhs; rhs } ->
      let dst' = fresh () in
      (Icmp { dst = dst'; cond; lhs = remap lhs; rhs = remap rhs }, (dst, dst'))
  | Call { dst; fn; args } ->
      begin match dst with
      | Some old_dst ->
          let dst' = fresh () in
          (Call { dst = Some dst'; fn; args = List.map remap args }, (old_dst, dst'))
      | None ->
          (Call { dst = None; fn; args = List.map remap args }, (-1, -1))
      end
  | Phi _ -> raise Exit
  | Shl { dst; lhs; rhs } ->
      let dst' = fresh () in
      (Shl { dst = dst'; lhs = remap lhs; rhs = remap rhs }, (dst, dst'))
  | AShr { dst; lhs; rhs } ->
      let dst' = fresh () in
      (AShr { dst = dst'; lhs = remap lhs; rhs = remap rhs }, (dst, dst'))
  | And { dst; lhs; rhs } ->
      let dst' = fresh () in
      (And { dst = dst'; lhs = remap lhs; rhs = remap rhs }, (dst, dst'))
  | Zext { dst; src } ->
      let dst' = fresh () in
      (Zext { dst = dst'; src = remap src }, (dst, dst'))
  | Copy { dst; src } ->
      let dst' = fresh () in
      (Copy { dst = dst'; src = remap src }, (dst, dst'))

let apply_unroll (f : func) (bmap : basic_block IntMap.t) (simple : simple_unroll_loop) =
  let next_label = ref (f.f_max_label + 1) in
  let next_vreg = ref (f.f_max_vreg + 1) in
  let fresh_label () = let x = !next_label in incr next_label; x in
  let fresh_vreg () = let x = !next_vreg in incr next_vreg; x in
  let spec = simple.counted in
  let body = simple.body in

  let header_bb = IntMap.find spec.header bmap in
  let body_bb = IntMap.find body bmap in
  let _, header_rest = partition_header_instrs header_bb in
  if header_rest = [] then raise Exit;

  let resolve curr rename = function
    | Imm _ as v -> v
    | Global _ as v -> v
    | VReg r ->
        match IntMap.find_opt r rename with
        | Some r' -> VReg r'
        | None ->
            match IntMap.find_opt r curr with
            | Some v -> v
            | None -> VReg r
  in

  let init_curr =
      List.fold_left (fun m phi -> IntMap.add phi.dst phi.init m)
      IntMap.empty spec.phis
  in

  let clones, final_curr, first_target, new_exit_pred =
    if spec.trip_count = 0 then
      ([], init_curr, spec.exit_block, spec.preheader)
    else
      let clone_labels = List.init spec.trip_count (fun _ -> fresh_label ()) in
      let targets = List.tl clone_labels @ [ spec.exit_block ] in
      let curr = ref init_curr in
      let built = ref [] in
      List.iter2 (fun lbl next_target ->
        let rename = ref IntMap.empty in
        let remap v = resolve !curr !rename v in
        let instrs =
          List.map (fun instr ->
            let cloned, (old_dst, new_dst) = clone_instr fresh_vreg remap instr in
            if old_dst >= 0 then rename := IntMap.add old_dst new_dst !rename;
            cloned
          ) body_bb.bb_instrs
        in
          curr := List.fold_left (fun m phi ->
            let latch_v =
              match find_latch_value body phi.latch_incomings with
              | Some v -> v
              | None -> raise Exit
            in
            IntMap.add phi.dst (remap latch_v) m
        ) IntMap.empty spec.phis;
        built := { bb_label = lbl; bb_instrs = instrs; bb_term = Jump next_target } :: !built
      ) clone_labels targets;
      (List.rev !built, !curr, List.hd clone_labels, List.hd (List.rev clone_labels))
  in

  let final_map r = IntMap.find_opt r final_curr in

  let remaining =
    IntMap.filter (fun lbl _ ->
        not (IntSet.mem lbl spec.blocks)
    ) bmap
    |> IntMap.map (fun bb ->
      let bb =
        { bb with
          bb_instrs = List.map (map_instr_values final_map) bb.bb_instrs;
          bb_term = map_term_values final_map bb.bb_term
        }
      in
      if bb.bb_label = spec.preheader then
        { bb with bb_term = rewrite_succ spec.header first_target bb.bb_term }
      else if bb.bb_label = spec.exit_block then
        let fix_instr = function
          | Phi p ->
                let incoming =
                  List.filter_map (fun (v, lbl) ->
                    if IntSet.mem lbl spec.blocks then
                      if lbl = spec.header then
                        Some (v, new_exit_pred)
                      else
                        None
                    else
                      Some (v, lbl)
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

  let all_blocks =
    List.fold_left (fun m bb -> IntMap.add bb.bb_label bb m) remaining clones
  in
  { f with
    f_blocks =
      IntMap.bindings all_blocks
      |> List.sort (fun (a, _) (b, _) -> compare a b);
    f_max_vreg = !next_vreg - 1;
    f_max_label = !next_label - 1;
  }

let run_on_func (f : func) : func =
  let rec fixpoint (f : func) =
    let bmap = build_bmap f in
    let dom = Dominance.analyze f in
    let li = Loop_info.analyze f dom in
    let loops =
      List.sort (fun a b ->
        let c = compare b.depth a.depth in
        if c <> 0 then c else compare a.header b.header
      ) li.loops
    in
      match List.find_map (fun lp ->
        match detect_counted_loop bmap lp with
        | None -> None
        | Some spec -> detect_simple_unroll_loop bmap spec
      ) loops with
      | None ->
          f
      | Some simple ->
          fixpoint (apply_unroll f bmap simple)
  in
  fixpoint f

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
