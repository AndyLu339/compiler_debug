(* ToyC 优化 — 重关联
   (a + C1) + C2 → a + (C1 + C2)，把常量聚集暴露更多折叠机会 *)

open Ir_types
open Common

module IntMap = Map.Make (Int)

let build_def_map (f : func) : instr IntMap.t =
  List.fold_left (fun acc (_, bb) ->
    List.fold_left (fun acc instr ->
      match instr_dst instr with
      | Some dst -> IntMap.add dst instr acc
      | None -> acc
    ) acc bb.bb_instrs
  ) IntMap.empty f.f_blocks

let normalize_commutative a b =
  match a, b with
  | Imm _, VReg _ -> b, a
  | _ -> a, b

let combine_imm op a b =
  match op with
  | Add -> Some (a + b)
  | Mul -> Some (a * b)
  | _ -> None

let peel_same_op_const (def_map : instr IntMap.t) (op : binary_op) (v : value)
    : (value * int) option =
  match v with
  | VReg r ->
      begin match IntMap.find_opt r def_map with
      | Some (Binop { op = op'; lhs; rhs; _ }) when op = op' ->
          begin match lhs, rhs with
          | Imm c, x
          | x, Imm c ->
              Some (x, c)
          | _ ->
              None
          end
      | _ ->
          None
      end
  | Imm _ | Global _ ->
      None

let rewrite_binop (def_map : instr IntMap.t) (op : binary_op) (lhs : value) (rhs : value)
    : value * value =
  match op with
  | Add | Mul ->
      let lhs, rhs = normalize_commutative lhs rhs in
      begin match lhs, rhs with
      | x, Imm c2 ->
          begin match peel_same_op_const def_map op x with
          | Some (base, c1) ->
              begin match combine_imm op c1 c2 with
              | Some c -> normalize_commutative base (Imm c)
              | None -> lhs, rhs
              end
          | None ->
              lhs, rhs
          end
      | _ ->
          lhs, rhs
      end
  | _ ->
      lhs, rhs

let run_on_func (f : func) : func =
  let def_map = build_def_map f in
  let new_blocks = List.map (fun (lbl, bb) ->
    let new_instrs = List.map (fun instr ->
      match instr with
      | Binop ({ op; lhs; rhs; _ } as b) ->
          let lhs, rhs = rewrite_binop def_map op lhs rhs in
          Binop { b with lhs; rhs }
      | _ ->
          instr
    ) bb.bb_instrs in
    (lbl, { bb with bb_instrs = new_instrs })
  ) f.f_blocks in
  { f with f_blocks = new_blocks }

let run (m : module_) : module_ =
  { m with m_funcs = List.map (fun (n, f) -> (n, run_on_func f)) m.m_funcs }
