(* Implementation of per-node dataflow frontier calculation based on the paper by Cooper et al.
 * (Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy. A simple, fast dominance algorithm.
 * Technical Report TR-06-33870, Department of Computer Science, Rice University, 2006.)
 *)
open Core

module CFG = Cfg
module VHT = CFG.Vertex.Table
module VHS = CFG.Vertex.Hash_set
module DT = Dominator_tree
module DFG = Graph.Make_Hash_Graph(CFG.Vertex)

type t = DFG.t

module Print =
struct
  let pp_dfg_graphvis_format = DFG.pp_graphvis_format ~v_to_str:(CFG.Print.pp_label)
end

let create_frontiers (cfg : 'a CFG.t) : t =
  let frontiers = DFG.create () in
  CFG.iter_label ~f:(fun ~label -> DFG.add_vertex_void frontiers label) cfg ;
  frontiers
;;

let add_to_frontier (frontiers : t) ~(node : CFG.label) ~(frontier_node : CFG.label) : unit =
  DFG.add_directed_edge_void frontiers ~src:node ~dest:frontier_node
;;

(* ------------------------------------- INTERFACE FUNCTIONS ------------------------------------ *)

let frontier_exn (frontiers : t) (label : CFG.label) : CFG.label List.t =
  DFG.nbor_list frontiers label
;;

let compute (cfg : 'a CFG.t) (rdt : DT.reverse_t) : t =
  let frontiers = create_frontiers cfg in
  let rec propagate_pred (node : CFG.label) (runner : CFG.label) (node_idom : CFG.label) =
    if CFG.equal_label node_idom runner then ()
    else 
      (add_to_frontier frontiers ~node:runner ~frontier_node:node ;
      Option.iter (DT.idom_exn rdt ~node:runner) ~f:(fun r' -> propagate_pred node r' node_idom) ;)
  in
  let propagate_node_to_frontiers ~label:node =
    let preds = CFG.preds cfg node in
    if (List.length preds) >= 2 then
      List.iter preds ~f:(fun p -> DT.idom_exn rdt ~node |> Option.iter ~f:(propagate_pred node p))
  in
  CFG.iter_label cfg ~f:propagate_node_to_frontiers ;
  frontiers
;;
