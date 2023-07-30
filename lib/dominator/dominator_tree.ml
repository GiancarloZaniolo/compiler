(* Implementation of a reverse-dominator tree based on the algorithm presented by Cooper et al. 
 * (Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy. A simple, fast dominance algorithm.
 * Technical Report TR-06-33870, Department of Computer Science, Rice University, 2006.)
 *)
open Core

module AS = Assem
module AL = Assem.Label
module CFG = Cfg
module VHT = CFG.Vertex.Table
module DT = Graph.Make_Hash_Graph(CFG.Vertex)

type indexed_label = { label : CFG.label ; preorder_idx : int [@ignore] } [@@deriving equal]
type dflow_value = UNDEFINED | Node of indexed_label [@@deriving equal]

type t = DT.t
type reverse_t = DT.t
type value_idom_tree = dflow_value VHT.t

module Print =
struct
  let pp_rdt_graphvis_format = DT.pp_graphvis_format ~v_to_str:(CFG.Print.pp_label)
  (* let pp_dflow_value = function
    | UNDEFINED -> "UNDEFINED"
    | Node indexed_label ->
        sprintf "{%d. %s}" indexed_label.preorder_idx (CFG.Print.pp_label indexed_label.label) *)
end


(* ------------------------------------- INTERFACE FUNCTIONS ------------------------------------ *)

let idom_exn (rdom_tree : reverse_t) ~(node : CFG.label) : CFG.label option =
  match DT.nbor_list rdom_tree node with
  | [] -> None
  | label :: [] -> Some label
  | _ :: _ ->
    sprintf "Node `%s` has more than one immediate dominator assigned" (CFG.Print.pp_label node)
    |> failwith
;;

let post_order ?(root=AL.ENTRY_LABEL) (dt : t) : CFG.label list =
  DT.reverse_postorder dt ~root |> List.rev
;;

let of_reverse_dt (rdt : reverse_t) : t = DT.transpose rdt

let compute_reverse_dt ?(root=AL.ENTRY_LABEL) (cfg : 'a CFG.t) : reverse_t =
  let value_tree : value_idom_tree = VHT.create () in
  let label_to_index : int VHT.t = VHT.create () in
  let reverse_post_order : CFG.label list = CFG.reverse_postorder_forward ~root cfg in
  let post_order : CFG.label list = reverse_post_order |> List.rev in
  List.iteri post_order
    ~f:(fun preorder_idx label -> VHT.add_exn label_to_index ~key:label ~data:preorder_idx);
  let indexed_cfg : indexed_label CFG.t =
    CFG.mapi cfg
      ~f:(fun ~label ~data ->
        let _ : 'a = data in { label ; preorder_idx = VHT.find_exn label_to_index label } )
  in
  let idom_value_exn ~(node : CFG.label) = VHT.find_exn value_tree node in
  (* While the two functitons below may look very similar, unrolling once allows us to reduce the
     number of hash set accesses we do to access the preorder index of the iterated predecessor *)
  let rec intersect_values (n1 : dflow_value) (n2 : dflow_value) : dflow_value =
    match (n1, n2) with
    | (UNDEFINED, _) -> n2
    | (_, UNDEFINED) -> n1 
    | (Node label_idx1, Node label_idx2) ->
      if label_idx1.preorder_idx = label_idx2.preorder_idx then n1
      else if label_idx1.preorder_idx < label_idx2.preorder_idx then
        let idom_n1 = idom_value_exn ~node:(label_idx1.label) in
        intersect_values idom_n1 n2 
      else
        let idom_n2 = idom_value_exn ~node:(label_idx2.label) in
        intersect_values n1 idom_n2
  in
  let intersect_label (n1 : dflow_value) (pred_label : CFG.label) : dflow_value =
    let label_idx2 = CFG.get_data_exn indexed_cfg ~label:pred_label in
    match n1 with
    | UNDEFINED -> Node label_idx2
    | Node label_idx1 ->
      if label_idx1.preorder_idx = label_idx2.preorder_idx then n1
      else if label_idx1.preorder_idx < label_idx2.preorder_idx then
        let idom_n1 = idom_value_exn ~node:(label_idx1.label) in
        intersect_values idom_n1 (Node label_idx2)
      else
        let idom_n2 = idom_value_exn ~node:(label_idx2.label) in
      intersect_values n1 idom_n2
  in
  let set_idom_value ~label idom = VHT.set value_tree ~key:label ~data:idom in
  let entry_value = 
    Node 
      { label = root
      ; preorder_idx = (CFG.get_data_exn indexed_cfg ~label:root).preorder_idx }
  in
  set_idom_value ~label:root entry_value ;
  let iter_labels = List.filter ~f:(Fn.compose not (phys_equal root)) reverse_post_order in
  List.iter iter_labels ~f:(fun label -> set_idom_value ~label UNDEFINED) ;
  let changed = ref true in
  while !changed do
    changed := false ;
    let process_label label =
      let preds = CFG.preds cfg label in
      let init_idom =
        (match preds with
        | [] -> UNDEFINED
        | p :: _ -> CFG.get_data_exn indexed_cfg ~label:p |> Node )
      in
      let new_idom = List.fold ~f:intersect_label ~init:init_idom preds in
      if VHT.find_exn value_tree label |> equal_dflow_value new_idom |> not then
        (set_idom_value ~label new_idom ;
        changed := true;)
    in
    List.iter iter_labels ~f:process_label ;
  done ;
  let val_to_label ~key ~data =
    match data with
    | UNDEFINED ->
      if CFG.equal_label key root then None
      else sprintf "CFG node `%s` not assigned an idom" (CFG.Print.pp_label key) |> failwith
    | Node n -> Some n.label
  in
  let rdt = DT.create () in
  let add_node_to_rdt node idom =
    match idom with
    | None -> let _ : DT.t = DT.add_vertex rdt node in ()
    | Some idom -> DT.add_directed_edge_void rdt ~src:node ~dest:idom
  in
  VHT.mapi ~f:val_to_label value_tree
  |> VHT.iteri ~f:(fun ~key ~data -> add_node_to_rdt key data) ;
  rdt
;;
