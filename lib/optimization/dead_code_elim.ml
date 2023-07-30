(* Dead Code Elimination. Will be expanded to include the SSA-based ADCE.
 * Author: Elan Biswas <elanb@andrew.cmu.edu>
 * TODO: fix description
 *)

open Core

module CFG = Cfg
module DT = Dominator_tree
module DFT = Dominance_frontier
module AS = Assem
module QWT = Assem.Quad_With_Temps

module AL = Assem.Label
module AL_HT = Assem.Label.Table
module AL_HS = Assem.Label.Hash_set

module STIR = Assem.Stack_Temp_Imm_Reg
module STIR_HT = STIR.Table
module STIR_HS = STIR.Hash_set

module HS = Hash_set
module Q = Queue

let clean_control_flow (cfg : QWT.program CFG.t) : unit =
  let replace_succ ~(pred : CFG.label) ~(succ : CFG.label) ~(with_ : CFG.label) =
    let replacement = if AL.equal with_ succ then pred else with_ in
    let pred_block' =
      (match CFG.get_data_exn ~label:pred cfg |> List.rev with
      | QWT.Goto _ :: prevs -> QWT.Goto replacement :: prevs
      | QWT.If i :: prevs ->
        (if AL.equal i.if_true i.if_false then (
          assert (AL.equal i.if_true succ) ;
          QWT.Goto replacement :: prevs
        ) else if (AL.equal i.if_true succ) then
          QWT.If { i with if_true = replacement} :: prevs
        else
          QWT.If { i with if_false = replacement } :: prevs)
      | instr :: _ ->
        sprintf "Expected last instruction of block to be a jump, got `%s` instead"
          (QWT.format instr)
        |> failwith
      | [] -> 
        sprintf "Expected non-empty start block in: `%s`->`%s`->`%s`"
          (CFG.Print.pp_label pred)
          (CFG.Print.pp_label succ)
          (CFG.Print.pp_label with_)
        |> failwith)
      |> List.rev
    in
    CFG.rem_succ ~pred ~succ cfg ;
    (* Even though in the code there is only one successor, this segment of code may be a loop
       Because loops may not exit, this may cause the entry node of the CFG to be disconnected from
       the exit. To resolve this, the CFG always adds the exit node as a successor to nodes that
       jump back to an ancestor. This invariant is set during initial translation, but may become
       invalid here if we do not add all of the replaced successor's successors to the predecessor
       successors. *)
    List.concat [ CFG.succs cfg succ ; [ replacement ] ]
    |> List.filter ~f:(Fn.compose not (AL.equal succ))
    |> List.iter ~f:(fun succ_succ -> CFG.set_succ ~pred ~succ:succ_succ cfg) ;
    CFG.set_data ~label:pred ~data:pred_block' cfg ;
  in

  let cfg_changed = ref true in
  let deleted_nodes : AL_HS.t = AL_HS.create () in

  let remove_if_empty (label : CFG.label) : unit =
    if HS.mem deleted_nodes label then () else
    (match CFG.get_data_exn ~label cfg with
    | QWT.Label (AL.Fn_label _) :: _ -> ()
    | [ QWT.Label cur_lbl ; QWT.Goto next_lbl ] ->
      assert (AL.equal label cur_lbl) ;
      CFG.preds cfg label
      |> List.iter ~f:(fun pred -> replace_succ ~pred ~succ:label ~with_:next_lbl) ;
      CFG.remove_node cfg label ;
      HS.add deleted_nodes label ;
      cfg_changed := true ;
    | _ -> ())
  in

  let combine_if_succ_has_one_pred ~(pred : CFG.label) ~(succ : CFG.label) : unit =
    if HS.mem deleted_nodes pred || HS.mem deleted_nodes succ then () else
    (match CFG.preds cfg succ with
    | [ p ] ->
      assert (AL.equal p pred) ;
      let pred_block = CFG.get_data_exn cfg ~label:pred in
      let pred_block_no_jmp = List.sub ~pos:0 ~len:(List.length pred_block - 1) pred_block in
      let succ_block = CFG.get_data_exn cfg ~label:succ in
      let block' =
        (match succ_block with
        | QWT.Label _ :: rest -> List.append pred_block_no_jmp rest
        | _ ->
          sprintf "Expected block to start with a label: `%s`" (CFG.Print.pp_label succ)|> failwith)
      in
      CFG.succs cfg succ
      |> List.iter ~f:(fun succ_succ -> replace_succ ~pred ~succ ~with_:succ_succ) ;
      CFG.set_data cfg ~label:pred ~data:block' ;
      CFG.remove_node cfg succ ;
      HS.add deleted_nodes succ ;
      cfg_changed := true ;
    | _ -> ())
  in

  let hoist_if_empty_branch ~(pred : CFG.label) ~(succ : CFG.label) : unit =
    if HS.mem deleted_nodes pred || HS.mem deleted_nodes succ then () else
    (match CFG.get_data_exn cfg ~label:succ with
    | [ QWT.Label _ ; (QWT.If i) as branch ] ->
      let pred_block = CFG.get_data_exn cfg ~label:pred in
      let pred_block' =
        List.append (List.sub ~pos:0 ~len:(List.length pred_block - 1) pred_block) [ branch ]
      in
      CFG.set_data cfg ~label:pred ~data:pred_block' ;
      CFG.succs cfg pred |> List.iter ~f:(fun succ -> CFG.rem_succ cfg ~pred ~succ) ;
      CFG.set_succ cfg ~pred ~succ:i.if_false ;
      CFG.set_succ cfg ~pred ~succ:i.if_true ;
    | _ -> () )  
  in

  let clean_node (label : CFG.label) : unit =
    if HS.mem deleted_nodes label then () else
    (match CFG.get_data_exn ~label cfg |> List.rev with
    | QWT.If i :: rest ->
      if AL.equal i.if_false i.if_true then
        let block' = QWT.Goto i.if_false :: rest |> List.rev in
        CFG.set_data cfg ~label ~data:block'
    | QWT.Goto ((AL.Local_label _) as next_lbl) :: _ ->
      remove_if_empty label ;
      combine_if_succ_has_one_pred ~pred:label ~succ:next_lbl ;
      hoist_if_empty_branch ~pred:label ~succ:next_lbl ;
    | QWT.Goto (AL.MEM_LABEL | AL.ARITH_LABEL) :: _ ->
      remove_if_empty label ;
    | _ -> ())
  in

  while !cfg_changed do
    cfg_changed := false ;
    HS.clear deleted_nodes ;
    CFG.reverse_postorder_backward cfg |> List.iter ~f:clean_node ;
  done ;
  CFG.remove_unreachable_nodes cfg ;
;;

let remove_dead_phi_srcs (cfg : QWT.program CFG.t) : QWT.program CFG.t =
  let src_label_is_dead label = CFG.mem_label cfg label in
  let remove_dead_phi_srcs_bb basic_block = 
    let rec remove_dead_phi_srcs_acc remaining acc =
      match remaining with
      | [] -> acc
      | (QWT.Phi phi) :: rest  ->
        let acc' =
          QWT.Phi { phi with srcs = STIR_HT.map phi.srcs ~f:(HS.filter ~f:src_label_is_dead) }
          :: acc
        in
        remove_dead_phi_srcs_acc rest acc'
      | instr :: rest -> remove_dead_phi_srcs_acc rest (instr :: acc)
    in
    remove_dead_phi_srcs_acc basic_block [] |> List.rev
  in
  CFG.map_data cfg ~f:(remove_dead_phi_srcs_bb)

(* =============================== Agressive Deadcode Elimination =============================== *)

type instr_info = { used_temps : STIR_HS.t ; block_label : AL.t ; phi_src_lbls : AL_HS.t }
type useful_env =
  { useful_temps : STIR_HS.t
  ; useful_block_labels : AL_HS.t
  ; useful_branch_labels : AL_HS.t
  }

let stir_is_temp = function STIR.Temp _ -> true | _ -> false

let temp_or_addr_mode_to_temps = function
  | STIR.Addr_mode exp -> [ STIR.Temp exp.base ; STIR.Temp exp.index ]
  | (STIR.Temp _) as t -> [ t ]
  | _ -> failwith "Expected a temp or address mode expression"

let used_temps_of_instr (instr : QWT.instr) : STIR_HS.t =
  (match instr with
  | QWT.Binop bop -> [ bop.lhs ; bop.rhs ]
  | QWT.Unop uop ->
    (match uop.op with | AS.LEA -> temp_or_addr_mode_to_temps uop.src | _ -> [ uop.src ])
  | QWT.Mov mov -> [ mov.src ]
  | QWT.Phi phi -> STIR_HT.keys phi.srcs
  | QWT.If i -> [ i.rhs ; i.lhs ]
  | QWT.Call c -> c.fn_label.param_temps |> List.map ~f:(fun t -> STIR.Temp t)
  | QWT.Return (Some t) -> [ t ]
  | QWT.Mem_read load -> temp_or_addr_mode_to_temps load.src
  | QWT.Mem_write store -> store.src :: temp_or_addr_mode_to_temps store.dest
  | (QWT.Return None|QWT.Goto _|QWT.Label _|QWT.Directive _|QWT.Comment _) -> [])
  |> List.filter ~f:stir_is_temp |> STIR_HS.of_list

let assert_all_are_temps (temps : STIR.t List.t) : STIR.t List.t =
  List.iter ~f:(fun t -> assert (stir_is_temp t)) temps ;
  temps

let def_temps_of_instr (instr : QWT.instr) : STIR.t List.t =
  (match instr with
  | QWT.Binop bop -> [ bop.dest ]
  | QWT.Unop uop -> [ uop.dest ]
  | QWT.Mov mov -> [ mov.dest ]
  | QWT.Phi phi -> [ phi.dest ]
  | QWT.Call c -> (match c.dest with
    | Some dest -> [ STIR.Temp dest ]
    | None -> [])
  | QWT.Mem_read load -> [ load.dest ]
  | QWT.Label (AL.Fn_label fn) -> fn.param_temps |> List.map ~f:(fun t -> STIR.Temp t)
  | (QWT.Return _|QWT.Mem_write _|QWT.If _|QWT.Goto _|QWT.Label _|QWT.Directive _|QWT.Comment _) ->
    [])
  |> assert_all_are_temps

(* From Engineering a Compiler, 2nd Edition Chapter 10.1: An instruction is critical if it
   sets the return value of the procedure or it affects the value of a storage location that may
   be accessible from outside the current procedure.*)
let instr_is_critical (instr : QWT.instr) (purity_fn : Symbol.t -> bool) : bool = (*&&*)
  match instr with
  | QWT.Return _ (* because it sets the return value *)
  | QWT.Mem_write _  -> true(* because other procedures may be able to access the value stored *)
  | QWT.Call c -> not (purity_fn c.fn_label.name)
  | QWT.If i ->
    (match (i.if_false, i.if_true) with
    | ((AL.ARITH_LABEL, _) | (AL.MEM_LABEL, _) | (_, AL.ARITH_LABEL) | (_, AL.MEM_LABEL)) -> true
    | _ -> false)
  | QWT.Goto (AL.ARITH_LABEL | AL.MEM_LABEL) -> true
  | QWT.Binop bop ->
    (match bop.op with
    | AS.Div | AS.Mod -> true (* Because it can have side effect *)
    | (AS.Add|AS.Sub|AS.Mul|AS.BWAnd|AS.BWOr|AS.BWXor|AS.LShift|AS.RShift|AS.RShift_unsigned) ->
      false)
  | (QWT.Unop _|QWT.Mov _|QWT.Phi _|QWT.Mem_read _|QWT.Goto _|QWT.Label _
    |QWT.Directive _|QWT.Comment _) -> false

let temp_is_marked_useful useful_temps temp = assert (stir_is_temp temp); HS.mem useful_temps temp
;;

let label_is_marked_useful useful_labels label = HS.mem useful_labels label
;;

let used_temps_of_label_end_branch (cfg : QWT.program CFG.t) (label : CFG.label) : STIR.t list =
  (match CFG.get_data_exn cfg ~label |> List.rev with
  | QWT.Goto _ :: _ -> []
  | QWT.If i :: _ -> [ i.rhs ; i.lhs ]
  | _ -> 
    sprintf
      "Got an unexpected basic block with either a missing end-jump or missing label. Label: `%s`"
      (CFG.Print.pp_label label)
    |> failwith
  )
  |> List.filter ~f:stir_is_temp
;;

let mark_useful_instrs (cfg : QWT.program CFG.t) (rdft : DFT.t) (purity_fn : Symbol.t -> bool)
    : useful_env =
  let def_to_info : instr_info STIR_HT.t = STIR_HT.create () in
  let map_def_to_uses_bb ~(label : CFG.label) : unit =
    let rec map_def_to_uses_rec remaining =
      match remaining with
      | [] -> ()
      | instr :: rest ->
        let used_temps = used_temps_of_instr instr in
        let block_label = label in
        let phi_src_lbls =
          (match instr with
          | QWT.Phi phi ->
              STIR_HT.data phi.srcs
              |> List.fold ~f:(HS.union) ~init:(AL_HS.create ())
          | _ -> AL_HS.create ())
        in
        let info : instr_info = { used_temps ; block_label ; phi_src_lbls } in
        let def_temps = def_temps_of_instr instr in
        List.iter def_temps ~f:(fun def -> STIR_HT.add_exn def_to_info ~key:def ~data:info) ;
        map_def_to_uses_rec rest
    in
    let basic_block = CFG.get_data_exn cfg ~label in
    map_def_to_uses_rec basic_block
  in
  
  let work_list : STIR.t Q.t = Q.create () in
  let useful_temps : STIR_HS.t = STIR_HS.create () in
  let useful_branch_labels : AL_HS.t = AL_HS.create () in
  let useful_block_labels : AL_HS.t = AL_HS.create () in

  let mark_temp_useful temp = assert (stir_is_temp temp); HS.add useful_temps temp in
  let mark_branch_label_useful label = HS.add useful_branch_labels label in
  let mark_block_label_useful label = HS.add useful_block_labels label in

  let mark_temp_useful_and_enq_if_unmarked temp =
    if not (temp_is_marked_useful useful_temps temp) then (
      mark_temp_useful temp ;
      Q.enqueue work_list temp ;
    )
  in
  let rec mark_branch_useful_and_enq_if_unmarked label =
    if not (label_is_marked_useful useful_branch_labels label) then (
      mark_branch_label_useful label ;
      mark_block_label_useful label ;
      let label_end_branch_used_temps = used_temps_of_label_end_branch cfg label in
      let branch_rdf = DFT.frontier_exn rdft label in
      List.iter branch_rdf ~f:mark_branch_useful_and_enq_if_unmarked ;
      List.iter label_end_branch_used_temps ~f:(mark_temp_useful_and_enq_if_unmarked) ;
    )
  in
  let init_work_list_bb ~(label : CFG.label) : unit =
    let rec init_work_list_rec remaining =
      match remaining with
      | [] -> ()
      | instr :: rest ->
        if instr_is_critical instr purity_fn then (
          let defs = def_temps_of_instr instr in
          let uses = used_temps_of_instr instr in
          let rdf_labels = DFT.frontier_exn rdft label in
          List.iter defs ~f:(mark_temp_useful_and_enq_if_unmarked) ;
          HS.iter uses ~f:(mark_temp_useful_and_enq_if_unmarked) ;
          List.iter ~f:mark_branch_useful_and_enq_if_unmarked rdf_labels ;
          mark_block_label_useful label ;
        ) ;
        init_work_list_rec rest ;
    in
  let basic_block = CFG.get_data_exn ~label cfg in
  init_work_list_rec basic_block;
  in
  CFG.iter_label cfg ~f:map_def_to_uses_bb ;
  CFG.iter_label cfg ~f:init_work_list_bb ;
  while not (Q.is_empty work_list) do
    let cur_temp = Q.dequeue_exn work_list in
    let info = STIR_HT.find_exn def_to_info cur_temp in
    let block_rdf = DFT.frontier_exn rdft info.block_label in
    HS.iter info.used_temps ~f:(mark_temp_useful_and_enq_if_unmarked) ;
    HS.iter info.phi_src_lbls ~f:(mark_block_label_useful) ;
    let block_and_phi_rdf =
      HS.to_list info.phi_src_lbls |> List.concat_map ~f:(DFT.frontier_exn rdft)
      |> List.append block_rdf
    in
    List.iter ~f:mark_branch_useful_and_enq_if_unmarked block_and_phi_rdf ;
    mark_block_label_useful info.block_label ;
  done ;
  { useful_temps ; useful_branch_labels ; useful_block_labels }
;;

let sweep_useless_instrs
    (cfg : QWT.program CFG.t)
    (useful_info : useful_env)
    (rev_dom_tree : DT.reverse_t)
    (purity_fn : Symbol.t -> bool)
    : unit =
  let useful_temps : STIR_HS.t = useful_info.useful_temps in
  let useful_branch_labels : AL_HS.t = useful_info.useful_branch_labels in
  let useful_block_labels : AL_HS.t = useful_info.useful_block_labels in
  let nearest_marked_post_dominator label =
    let rec nearest_postdom_rec cur_lbl = 
      let post_idom = DT.idom_exn rev_dom_tree ~node:cur_lbl |> Option.value_exn in
      match post_idom with
      | AL.EXIT_LABEL -> None
      | post_idom ->
        (if label_is_marked_useful useful_block_labels post_idom then Some post_idom
        else nearest_postdom_rec post_idom)
    in
    nearest_postdom_rec label 
  in
  let sweep_bb label =
    let rec sweep_bb_acc (remaining : QWT.program) (acc : QWT.program) : QWT.program =
      match remaining with
      | [] -> acc
      | ((QWT.Binop _|Unop _|Mov _|Phi _|Call _|Mem_read _) as instr) :: rest ->
        let defs = def_temps_of_instr instr in
        let def_is_useful _ def =
          let open Continue_or_stop in
          if temp_is_marked_useful useful_temps def then Stop true
          else Continue ()
        in
        let instr_is_useful =
          List.fold_until ~f:(def_is_useful) ~init:() ~finish:(fun () -> false) defs
        in
        if instr_is_useful || instr_is_critical instr purity_fn then
          sweep_bb_acc rest (instr :: acc)
        else sweep_bb_acc rest acc
      | [ (QWT.If i) as instr ] ->
        (if not (label_is_marked_useful useful_branch_labels label) then (
          let (instr', new_goto_lbl) =
            (match nearest_marked_post_dominator label with
            | Some new_goto_lbl ->
              (QWT.Goto new_goto_lbl, new_goto_lbl)
            | None -> (QWT.Return None, AL.EXIT_LABEL))
          in
          CFG.rem_succ cfg ~pred:label ~succ:(i.if_false) ;
          CFG.rem_succ cfg ~pred:label ~succ:(i.if_true) ;
          CFG.set_succ cfg ~pred:label ~succ:new_goto_lbl ;
          instr' :: acc
        ) else instr :: acc)
    | instr :: rest -> sweep_bb_acc rest (instr :: acc)
    in
    let basic_block = CFG.get_data_exn cfg ~label in
    let basic_block' = sweep_bb_acc basic_block [] |> List.rev in
    CFG.set_data cfg ~label ~data:(basic_block')
  in
  let labels = CFG.get_all_labels cfg in
  List.iter labels ~f:(sweep_bb)

let adce (cfg : QWT.program CFG.t) (purity_fn : Symbol.t -> bool) : unit =
  let rev_cfg = CFG.reverse cfg in
  let rev_dom_tree = DT.compute_reverse_dt ~root:(AL.EXIT_LABEL) rev_cfg in
  let rev_dominance_frontier_tree = DFT.compute rev_cfg rev_dom_tree in
  let useful_info : useful_env = mark_useful_instrs cfg rev_dominance_frontier_tree purity_fn in
  sweep_useless_instrs cfg useful_info rev_dom_tree purity_fn ;
  CFG.remove_unreachable_nodes cfg
