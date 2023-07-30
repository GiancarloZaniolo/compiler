(* Implementation of the dataflow framework algorithm as presented by the Purple Dragon Book
 * (Compilers: Principles, Techniques, and Tools, 2nd Edition) 9.3.3
 * Author: Elan Biswas <elanb@andrew.cmu.edu>
 *)
open Core

module CFG = Cfg
module AL = Assem.Label
module VHT = Cfg.Vertex.Table

type 'value in_out = { in_val : 'value ; out_val : 'value }

type direction = FORWARD | BACKWARD

let dataflow_analyze
    (cfg : 'block CFG.t)
    ~(dir : direction)
    ~(top: unit -> 'value)
    ~(meet : 'value -> 'value -> 'value)
    ~(transfer : (CFG.label -> 'value -> 'value))
    ~(v_boundary : unit -> 'value)
    ~(eq : 'value -> 'value -> bool)
    : 'value in_out CFG.t =
  let outs = VHT.create () in
  let ins = VHT.create () in
  let (start_node, get_propagating_nbors, meet_results_map, transfer_result_map, rev_postorder) =
    match dir with
    | FORWARD -> (AL.ENTRY_LABEL, CFG.preds cfg, ins, outs, CFG.reverse_postorder_forward)
    | BACKWARD -> (AL.EXIT_LABEL, CFG.succs cfg, outs, ins, CFG.reverse_postorder_backward)
  in
  VHT.set ins ~key:start_node ~data:(v_boundary ()) ;
  VHT.set outs ~key:start_node ~data:(v_boundary ()) ;
  let labels = rev_postorder cfg |> List.filter ~f:(Fn.compose not (phys_equal start_node)) in
  List.iter labels ~f:(fun label -> VHT.set transfer_result_map ~key:label ~data:(top ())) ;
  let has_changed = ref true in
  while !has_changed do
    has_changed := false ;
    let update_label (label : CFG.label) : unit =
      let fold_meet in_acc nbor = VHT.find_exn transfer_result_map nbor |> meet in_acc in
      let new_meet_result = List.fold ~f:fold_meet ~init:(top ()) (get_propagating_nbors label) in
      let old_transfer_result = VHT.find_exn transfer_result_map label in
      let new_transfer_result = transfer label new_meet_result in
      (if not (eq old_transfer_result new_transfer_result) then has_changed := true) ;
      VHT.set meet_results_map ~key:label ~data:new_meet_result;
      VHT.set transfer_result_map ~key:label ~data:new_transfer_result;
    in
    List.iter labels ~f:update_label ;
  done ;
  let label_to_in_out (label : CFG.label) : 'value in_out =
    { in_val = VHT.find_exn ins label ; out_val = VHT.find_exn outs label }
  in
  CFG.remap_labels cfg ~f:(fun ~label -> label_to_in_out label)
