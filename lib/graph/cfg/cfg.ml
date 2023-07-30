(* Control flow graph library.
 * Authors:
 * - Elan Biswas <elanb@andrew.cmu.edu>
 * - Giancarlo Zaniolo <gzaniolo@andrew.cmu.edu>
 *)

open Core

type label = Assem.Label.t [@@deriving hash, sexp, compare, equal]

module L = Assem.Label
module Vertex = L
module AS = Assem
module VHT = L.Table
module VHS = L.Hash_set
module HS = Hash_set
module CFG = Graph.Make_Hash_Graph(L)

module Edge =
struct
  module T = struct
    type t = label * label [@@deriving hash, compare, sexp]
  end
  include T
  include Hashable.Make(T)
end

type 'a t = 
  { forward : CFG.t ; reverse : CFG.t ; label_to_data : 'a VHT.t ; fn_label : L.fn_label }
type 'a program = ('a t) List.t

module Print =
struct

let pp_label = function
  | L.Local_label label ->
    Local_label.name label |> String.substr_replace_first ~pattern:"." ~with_:""
  | L.Fn_label label -> Symbol.name label.name
  | L.ENTRY_LABEL -> "ENTRY"
  | L.EXIT_LABEL -> "EXIT"
  | L.MEM_LABEL -> "MEM"
  | L.ARITH_LABEL -> "ARITH"

  let pp_cfg_labels_only g = CFG.pp_graph g.forward ~v_to_str:pp_label

  let pp_cfg_graphvis_format g = CFG.pp_graphvis_format g.forward ~v_to_str:(pp_label)

  let pp_cfgs_graphvis_format gs = Print_utils.pp_list ~f:pp_cfg_graphvis_format ~sep:"\n" gs
  
  let pp_data g ~data_to_str =
    let pp_pair (label, data) = sprintf "%s\n%s" (pp_label label) (data_to_str data) in
    (VHT.to_alist g.label_to_data) |> Print_utils.pp_list ~sep:"\n" ~f:pp_pair
end

let create (fn_label : L.fn_label) : 'a t =
  { forward = CFG.create ()
  ; reverse = CFG.create ()
  ; label_to_data = VHT.create ()
  ; fn_label = fn_label 
  }

let succs (g : 'a t) label : L.t list = CFG.nbor_list g.forward label
let preds (g : 'a t) label : L.t list = CFG.nbor_list g.reverse label 

let get_fn_label (g : 'a t) : L.fn_label = g.fn_label

let mem_label (g : 'a t) (label : label) : bool = VHT.mem g.label_to_data label

let set_succ (g : 'a t) ~(pred : label) ~(succ : label) : unit =
  CFG.add_directed_edge_void g.forward ~src:pred ~dest:succ ;
  CFG.add_directed_edge_void g.reverse ~src:succ ~dest:pred

let rem_succ (g : 'a t) ~(pred : label) ~(succ : label) : unit =
  CFG.remove_directed_edge_void g.forward ~src:pred ~dest:succ ;
  CFG.remove_directed_edge_void g.reverse ~src:succ ~dest:pred

let set_data (g : 'a t) ~(label : label) ~(data : 'a) : unit =
  VHT.set g.label_to_data ~key:label ~data

let get_data_exn (g : 'a t) ~(label : label) : 'a = VHT.find_exn g.label_to_data label

let get_all_labels (g : 'a t) : label list = VHT.keys g.label_to_data

let map_data (g : 'a t) ~(f : 'a -> 'b) : 'b t =
  { g with label_to_data = VHT.map ~f g.label_to_data }

let mapi (g : 'a t) ~(f : label:label -> data:'a -> 'b) : 'b t =
  { g with label_to_data = VHT.mapi ~f:(fun ~key ~data -> f ~label:key ~data) g.label_to_data }

let merge_data_exn (g1 : 'a t) (g2 : 'b t) ~(f : label:label -> 'a -> 'b -> 'c) : 'c t =
  let merge_both_only ~key = function
    | `Both (a, b) -> f ~label:key a b |> Some
    | `Left _ -> sprintf "Label not present in right CFG: %s" (Print.pp_label key) |> failwith
    | `Right _ -> sprintf "Label not present in left CFG: %s" (Print.pp_label key) |> failwith
  in
  { g1 with label_to_data = VHT.merge g1.label_to_data g2.label_to_data ~f:merge_both_only }

let remap_labels (g : 'a t) ~(f : label:label -> 'b) : 'b t =
  let new_label_data key _ = f ~label:key in
  { g with label_to_data = VHT.mapi g.label_to_data ~f:(fun ~key ~data -> new_label_data key data) }

let iter ~(f:'a -> unit) (cfg : 'a t) : unit = VHT.iter ~f cfg.label_to_data

let iteri ~(f: label:label -> data:'a -> unit) (cfg : 'a t) : unit =
  VHT.iteri ~f:(fun ~key ~data -> f ~label:key ~data) cfg.label_to_data

let iter_label ~(f: label:label -> unit) (cfg : 'a t) : unit =
  VHT.iter_keys ~f:(fun label -> f ~label) cfg.label_to_data

let iter_forward_edge_srcs ~(f: label:label -> unit) (cfg : 'a t) : unit = 
  CFG.iter_verts ~f:(fun label -> f ~label) cfg.forward

let reverse_postorder_forward ?(root=Assem.Label.ENTRY_LABEL) (cfg : 'a t) : label list =
    CFG.reverse_postorder cfg.forward ~root

let reverse_postorder_backward ?(root=Assem.Label.EXIT_LABEL) (cfg : 'a t) : label list =
  CFG.reverse_postorder cfg.reverse ~root

let reverse (g : 'a t) : 'a t = { g with forward = g.reverse ; reverse = g.forward }

let remove_node (cfg : 'a t) (label : label) : unit =
  VHT.remove cfg.label_to_data label ;
  CFG.remove_vertex_exn_void cfg.forward label ;
  CFG.remove_vertex_exn_void cfg.reverse label

let remove_unreachable_nodes (cfg : 'a t) : unit =
  let reachable_nodes = reverse_postorder_forward cfg |> VHS.of_list in
  VHT.keys cfg.label_to_data
  |> List.iter ~f:(fun lbl -> if not (HS.mem reachable_nodes lbl) then remove_node cfg lbl)
