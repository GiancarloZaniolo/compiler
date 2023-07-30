(* Partial Redundancy Elimination.
 * Implemenation from Compilers: Principle, Techniques, and Tools, 2nd Edtion (Purple Dragon Book)
 * Chapter 9.5.
 *
 * Author: Elan Biswas <elanb@andrew.cmu.edu>
 *)
open Core

module AS = Assem
module AL = Assem.Label
module QWT = Assem.Quad_With_Temps
module STIR = Assem.Stack_Temp_Imm_Reg
module CFG = Cfg

module Expression =
struct
  module T  =
  struct
    type t =
      { op : AS.quad_arith_binop ; lhs : STIR.t ; rhs : STIR.t }
      [@@deriving hash, sexp, compare, equal]
  end
  include T
  include Hashable.Make(T)
  include Comparable.Make(T)

  let pp_expression exp =
    sprintf "%s %s %s"
      (STIR.format_operand exp.lhs) (QWT.format_arith_binop exp.op) (STIR.format_operand exp.rhs)
end

module EHT = Expression.Table
module EHS = Expression.Hash_set
module ES = Expression.Set
module SHT = STIR.Table
module HS = Hash_set

type uses_kills = { uses : ES.t ; kills : ES.t }

module DFlow = Dataflow
(* Used for anticipated expressions, available expressions, and postponable expressions *)
type dflow_value = UNIVERSE | Exp_set of ES.t [@@deriving equal]

(* ---------------------------------- DATAFLOW SET COMBINATORS ---------------------------------- *)
let dataflow_intersect (v1 : dflow_value) (v2 : dflow_value) : dflow_value =
  match (v1, v2) with
  | (UNIVERSE, _) -> v2
  | (_, UNIVERSE) -> v1
  | (Exp_set s1, Exp_set s2) -> Exp_set (ES.inter s1 s2)
let dataflow_union (v1 : dflow_value) (v2 : dflow_value) : dflow_value =
  match (v1, v2) with
  | (UNIVERSE, _) | (_, UNIVERSE) -> UNIVERSE
  | (Exp_set s1, Exp_set s2) -> Exp_set (ES.union s1 s2)
let dataflow_diff (v1 : dflow_value) (v2 : dflow_value) : dflow_value =
  match (v1, v2) with
  | (UNIVERSE, _) ->
    failwith "By the construction of dataflow, should never subtract from the universal set"
  | (_, UNIVERSE) -> Exp_set (ES.empty)
  | (Exp_set s1, Exp_set s2) -> Exp_set (ES.diff s1 s2)

(* -------------------------------- END DATAFLOW SET COMBINATORS -------------------------------- *)
(* ---------------------------------- PREPROCESSING FUNCTIONS ----------------------------------- *)

let split_edges (cfg : QWT.program CFG.t) : unit =
  let split_succ_if_has_mult_preds ~pred ~succ =
    match succ with
    | AL.EXIT_LABEL -> ()
    | AL.ENTRY_LABEL -> failwith "Entry label should never be a successor"
    | (AL.MEM_LABEL|AL.ARITH_LABEL|AL.Local_label _|AL.Fn_label _) ->
      if CFG.preds cfg succ |> List.length > 1 then
        let new_block_lbl = AL.Local_label (Local_label.create ()) in
        let lbl_instr = QWT.Label new_block_lbl in
        let goto_instr = QWT.Goto succ in
        CFG.set_data cfg ~label:(new_block_lbl) ~data:([ lbl_instr ; goto_instr ]) ;
        CFG.rem_succ cfg ~pred ~succ ;
        CFG.set_succ cfg ~pred ~succ:new_block_lbl ;
        CFG.set_succ cfg ~pred:new_block_lbl ~succ ;
        (* TODO: Is there a way not to do this casing? Initial thought may be getting rid of the
           jump instructions from the CFG, but then the CFG loses conditional jump info *)
        let pred_block' =
          (match CFG.get_data_exn cfg ~label:pred |> List.rev with
          | QWT.Goto _ :: prevs -> QWT.Goto new_block_lbl :: prevs |> List.rev
          | QWT.If i :: prevs ->
            let updated_if =
              (if AL.equal i.if_true succ then
                QWT.If { i with if_true = new_block_lbl }
              else
                QWT.If { i with if_false = new_block_lbl })
            in
            updated_if :: prevs |> List.rev
          | instr :: _ ->
            sprintf "Exptected a jump at the end of basic block. Got `%s` instead"
              (QWT.format instr) |> failwith
          | [] -> failwith "Expected a non-empty block")
        in
        CFG.set_data cfg ~label:pred ~data:pred_block'
  in
  let split_succ_edges (pred : CFG.label) : unit =
    CFG.succs cfg pred |> List.iter ~f:(fun succ -> split_succ_if_has_mult_preds ~pred ~succ)
  in
  CFG.get_all_labels cfg |> List.iter ~f:split_succ_edges

let exp_of_binop (binop : STIR.t AS.quad_binop) : Expression.t =
  {op = binop.op ; lhs = binop.lhs ; rhs = binop.rhs }

let compute_exp_uses_kills (cfg : QWT.program CFG.t) : uses_kills CFG.t =
  let map_stirs_to_exps (cfg : QWT.program CFG.t) : ES.t SHT.t =
    let stirs_to_exps = SHT.create () in
    let map_stirs_in_instr (instr : QWT.instr) : unit =
      match instr with
      | QWT.Phi _ -> failwith "PRE analysis doesn't currently support SSA form (found phi fn)"
      | QWT.Binop op ->
        let lhs = STIR.resize_64 op.lhs in
        let rhs = STIR.resize_64 op.rhs in
        let lhs_exps = SHT.find_or_add stirs_to_exps lhs ~default:(fun () -> ES.empty) in
        let rhs_exps = SHT.find_or_add stirs_to_exps rhs ~default:(fun () -> ES.empty) in
        let exp = exp_of_binop op in
        SHT.set stirs_to_exps ~key:lhs ~data:(ES.add lhs_exps exp) ;
        SHT.set stirs_to_exps ~key:rhs ~data:(ES.add rhs_exps exp) ;
      (* TODO: Pure functions and some (which?) memory reads can also be PRE candidates *)
      | (QWT.Call _|QWT.Mem_read _|QWT.Unop _|QWT.Mov _|QWT.If _|QWT.Return _|QWT.Mem_write _
        |QWT.Goto _|QWT.Directive _|QWT.Comment _|QWT.Label _) -> ()
    in
    let map_stirs_in_block (block : QWT.program) : unit =
      List.iter block ~f:(map_stirs_in_instr)
    in
    CFG.iter cfg ~f:(map_stirs_in_block) ;
    stirs_to_exps
  in
  let stirs_to_exps = map_stirs_to_exps cfg in
  let uses_kills_of_instr (acc : uses_kills) (instr : QWT.instr) : uses_kills =
    let update_kills dest =
      let dest_64 = STIR.resize_64 dest in
      ES.union acc.kills (SHT.find_or_add stirs_to_exps dest_64 ~default:(fun () -> ES.empty))
    in
    let update_uses exp = if ES.mem acc.kills exp then acc.uses else ES.add acc.uses exp in
    match instr with
    | QWT.Phi _ -> failwith "PRE analysis doesn't currently support SSA form (found phi fn)"
    | QWT.Binop op -> 
      { uses = update_uses (exp_of_binop op) ; kills = update_kills op.dest }
    | QWT.Mov mov -> { acc with kills = update_kills mov.dest }
    (* TODO: Pure functions and some (which?) memory reads can also be PRE candidates *)
    | QWT.Mem_read load -> { acc with kills = update_kills load.dest }
    | QWT.Call c -> (match c.dest with 
      | Some dest -> { acc with kills = update_kills (STIR.Temp dest) }
      | None -> acc)
    | QWT.Unop unop -> { acc with kills = update_kills unop.dest }
    | (QWT.If _|QWT.Return _|QWT.Mem_write _|QWT.Goto _|QWT.Directive _|QWT.Comment _
      |QWT.Label _) -> acc
  in
  let uses_kills_of_block (instrs : QWT.program) : uses_kills =
    let block_uses_kills_init : uses_kills = { uses = ES.empty ; kills = ES.empty } in
    let uses_kills = List.fold instrs ~f:uses_kills_of_instr ~init:block_uses_kills_init in
  uses_kills
  in
  CFG.map_data ~f:(uses_kills_of_block) cfg

(* -------------------------------- END PREPROCESSING FUNCTIONS --------------------------------- *)
(* -------------------------------------- DATAFLOW ANALYSES ------------------------------------- *)

let anticipated_expressions (uses_kills_cfg : uses_kills CFG.t) : dflow_value DFlow.in_out CFG.t =
  let transfer (label : CFG.label) (out_b : dflow_value) =
    let block_uses_kills = CFG.get_data_exn ~label uses_kills_cfg in
    dataflow_diff out_b (Exp_set block_uses_kills.kills)
    |> dataflow_union (Exp_set block_uses_kills.uses)
  in
  DFlow.dataflow_analyze
    uses_kills_cfg
    ~dir:(DFlow.BACKWARD)
    ~top:(fun () -> UNIVERSE)
    ~meet:(dataflow_intersect)
    ~transfer
    ~v_boundary:(fun () -> Exp_set ES.empty)
    ~eq:(equal_dflow_value)

let available_expressions
    ~(anticipated_cfg : dflow_value DFlow.in_out CFG.t)
    ~(uses_kills_cfg : uses_kills CFG.t)
    : dflow_value DFlow.in_out CFG.t =
  let transfer (label : CFG.label) (in_b : dflow_value) =
    let block_anticipated = CFG.get_data_exn ~label anticipated_cfg in
    let block_uses_kills = CFG.get_data_exn ~label uses_kills_cfg in
    let block_available_or_anticipated_in = dataflow_union (block_anticipated.in_val) in_b in
    dataflow_diff block_available_or_anticipated_in (Exp_set block_uses_kills.kills)
  in
  DFlow.dataflow_analyze
    anticipated_cfg
    ~dir:(DFlow.FORWARD)
    ~top:(fun () -> UNIVERSE)
    ~meet:(dataflow_intersect)
    ~transfer
    ~v_boundary:(fun () -> Exp_set ES.empty)
    ~eq:(equal_dflow_value)

(* The computation of an expression can be postponed to a block if an early placement of the
   expression exists on all paths leading to the block and there is no use of the expression after
   the placement. *)
let postponable_expressions
    ~(earliest_cfg : dflow_value CFG.t)
    ~(uses_kills_cfg : uses_kills CFG.t)
    : dflow_value DFlow.in_out CFG.t =
  let transfer (label : CFG.label) (in_b : dflow_value) =
    let earliest_b = CFG.get_data_exn ~label earliest_cfg in
    let uses_kills_b = CFG.get_data_exn ~label uses_kills_cfg in
    let postponable_candidates = dataflow_union earliest_b in_b in
    dataflow_diff postponable_candidates (Exp_set uses_kills_b.uses)
  in
  DFlow.dataflow_analyze
    earliest_cfg
    ~dir:(DFlow.FORWARD)
    ~top:(fun () -> UNIVERSE)
    ~meet:(dataflow_intersect)
    ~transfer
    ~v_boundary:(fun () -> Exp_set ES.empty)
    ~eq:(equal_dflow_value)

let used_expressions ~(uses_kills_cfg : uses_kills CFG.t) ~(latest_cfg : dflow_value CFG.t) =
  let transfer (label : CFG.label) (out_b : dflow_value) =
    let latest_b = CFG.get_data_exn ~label latest_cfg in
    let uses_kills_b = CFG.get_data_exn ~label uses_kills_cfg in
    let used_candidates = dataflow_union (Exp_set uses_kills_b.uses) out_b in
    dataflow_diff used_candidates latest_b
  in
  DFlow.dataflow_analyze
    latest_cfg 
    ~dir:(DFlow.BACKWARD)
    ~top:(fun () -> Exp_set ES.empty)
    ~meet:(dataflow_union)
    ~transfer
    ~v_boundary:(fun () -> Exp_set ES.empty)
    ~eq:(equal_dflow_value)

(* ------------------------------------ END DATAFLOW ANALYSES ----------------------------------- *)

(* In step 2 of the algorithm, we find the earliest position to compute a redundant expression
   without adding extra computation to any path. At a point p, the expressions that can be computed
   early are those that are anticipated (i.e. will be used on all paths leading from p) but are not
   yet available (i.e. already computed). *)
let earliest_of_anticipated_available_cfg
    ~(anticipated_cfg : dflow_value DFlow.in_out CFG.t)
    ~(available_cfg : dflow_value DFlow.in_out CFG.t)
    : dflow_value CFG.t =
  let merge_anticipated_available
      ~label
      (anticipated : dflow_value DFlow.in_out)
      (available : dflow_value DFlow.in_out)
      : dflow_value =
    let _ : CFG.label = label in
    dataflow_diff anticipated.in_val available.in_val
  in
  CFG.merge_data_exn anticipated_cfg available_cfg ~f:merge_anticipated_available

(* In step 3, we compute the position of the latest possible early computation of redundant
   expressions. The start of a block b is a valid computation point for a redundant expression e
   only if e is either in b's `earliest` set or its `postponable` set (i.e. the start of b is the
   earliest point that e can be computed without adding extra computation to a path, or postponing
   the computation of e to b from the earliest point does not un-eliminate the redundancy). The
   start of b is the `latest` possible computation point for e if the start of b is a valid
   computation point and the computation cannot be postponed past b. (i.e. either e is used in b or
   a successor of b is not a valid computation point for e.) *)
let latest_of_earliest_posts_uses
    ~(earliest_cfg : dflow_value CFG.t)
    ~(postponable_cfg : dflow_value DFlow.in_out CFG.t)
    ~(uses_kills_cfg : uses_kills CFG.t)
    : dflow_value CFG.t =
  let can_compute ~label : dflow_value =
    let earliest_b = CFG.get_data_exn earliest_cfg ~label in
    let postponable_b = CFG.get_data_exn postponable_cfg ~label in
    dataflow_union earliest_b postponable_b.in_val
  in
  let compute_latest_b ~label : dflow_value =
    let kills_uses_b = CFG.get_data_exn uses_kills_cfg ~label in
    let can_compute_b = can_compute ~label in
    let can_compute_and_used = dataflow_intersect can_compute_b (Exp_set kills_uses_b.uses) in
    let all_succs_can_compute =
      List.fold (CFG.succs earliest_cfg label)
        ~f:(fun acc label -> dataflow_intersect acc (can_compute ~label)) ~init:(UNIVERSE)
    in
    let can_compute_and_not_all_succs_can_compute =
      dataflow_diff can_compute_b all_succs_can_compute
    in
    dataflow_union can_compute_and_used can_compute_and_not_all_succs_can_compute
  in
  CFG.remap_labels earliest_cfg ~f:compute_latest_b

let eliminate_partial_redundancies (cfg : QWT.program CFG.t) : unit =
  split_edges cfg ;
  let uses_kills_cfg = compute_exp_uses_kills cfg in
  let anticipated_cfg = anticipated_expressions uses_kills_cfg in
  let available_cfg = available_expressions ~anticipated_cfg ~uses_kills_cfg in
  let earliest_cfg = earliest_of_anticipated_available_cfg ~anticipated_cfg ~available_cfg in
  let postponable_cfg = postponable_expressions ~earliest_cfg ~uses_kills_cfg in
  let latest_cfg = latest_of_earliest_posts_uses ~earliest_cfg ~postponable_cfg ~uses_kills_cfg in
  let used_cfg = used_expressions ~uses_kills_cfg ~latest_cfg in

  let exp_to_temp_map : Temp.t EHT.t = EHT.create () in
  let exp_to_stir_temp (exp : Expression.t) : STIR.t =
    let size = STIR.size_of exp.lhs in
    let temp = EHT.find_or_add exp_to_temp_map exp ~default:(Temp.create) in
    STIR.Temp { size ; temp }
  in
  let instr_of_exp (dest, exp : STIR.t * Expression.t) : QWT.instr =
    QWT.Binop { op = exp.op ; dest ; lhs = exp.lhs ; rhs = exp.rhs }
  in
  let prepend_exps_to_block (block : QWT.program) (exps : Expression.t list) : QWT.program =
    let instrs = List.map exps ~f:(fun e -> (exp_to_stir_temp e, e)) |> List.map ~f:instr_of_exp in
    match block with
    | (QWT.Label _) as lbl_instr :: rest -> lbl_instr :: (List.append instrs rest)
    | _ -> failwith "Expected first instruction of block to be a label" 
  in
  
  let find_and_replace (block : QWT.program) (exps : ES.t) : QWT.program =
    let rec replace_acc (instrs : QWT.program) (acc : QWT.program) : QWT.program =
      match instrs with
      | [] -> acc
      | QWT.Phi _ :: _ -> failwith "PRE analysis doesn't currently support SSA form (found phi fn)"
      | (QWT.Binop op) as instr :: rest ->
        let exp = exp_of_binop op in
        if ES.mem exps exp then
          QWT.Mov { src = exp_to_stir_temp exp ; dest = op.dest } :: acc |> replace_acc rest
        else
          replace_acc rest (instr :: acc)
      (* TODO: Pure functions and some (which?) memory reads can also be PRE candidates *)
      | (QWT.Call _|QWT.Mem_read _|QWT.Unop _|QWT.Mov _|QWT.If _|QWT.Return _|QWT.Mem_write _
        |QWT.Goto _|QWT.Directive _|QWT.Comment _|QWT.Label _) as instr :: rest -> 
        replace_acc rest (instr :: acc)
    in
    replace_acc block [] |> List.rev
  in

  let remove_redundancies label =
    match label with
    | AL.ARITH_LABEL | AL.MEM_LABEL | AL.EXIT_LABEL | AL.ENTRY_LABEL -> ()
    | AL.Fn_label _ | AL.Local_label _ ->
    let latest_b =
      match CFG.get_data_exn latest_cfg ~label with
      | UNIVERSE -> failwith "The dataflows values failed to converge to a set of expressions"
      | Exp_set s -> s
    in
    let used_b_out =
      match (CFG.get_data_exn used_cfg ~label).out_val with
      | UNIVERSE -> failwith "The dataflows values failed to converge to a set of expressions"
      | Exp_set s -> s
    in
    let uses_kills_b = CFG.get_data_exn uses_kills_cfg ~label in
    let uses_and_not_latest = ES.diff uses_kills_b.uses latest_b in
    let uses_and_used_later = ES.inter uses_kills_b.uses used_b_out in
    (* The replacements have to occur before prepending the computations because the replacement
       will overwrite the computation with the expression's temp *)
    let exps_to_replace = ES.union uses_and_not_latest uses_and_used_later in
    let block' = find_and_replace (CFG.get_data_exn cfg ~label) exps_to_replace in
    let exps_to_add = ES.inter latest_b used_b_out |> ES.to_list in
    let block'' = prepend_exps_to_block block' exps_to_add in
    CFG.set_data cfg ~label ~data:block'' ;
  in
  CFG.get_all_labels cfg |> List.iter ~f:remove_redundancies ;
