(* Control flow graph library.
 * Authors:
 * - Elan Biswas <elanb@andrew.cmu.edu>
 * - Giancarlo Zaniolo <gzaniolo@andrew.cmu.edu>
 *)

open Core

type label = Assem.Label.t [@@deriving hash, sexp, compare, equal]

type 'a t 
type 'a program = ('a t) List.t

module Vertex :
sig 
  type t = label [@@deriving hash, sexp, compare, equal]
  include Hashable.S with type t := t
end

module Edge :
sig
  type t = Vertex.t * Vertex.t [@@deriving hash, compare, sexp]
  include Hashable.S with type t := t
end

val create : Assem.Label.fn_label -> 'a t 

val succs : 'a t -> label -> label list
val preds : 'a t -> label -> label list

val set_succ : 'a t -> pred:label -> succ:label -> unit

val rem_succ : 'a t -> pred:label -> succ:label -> unit

val set_data : 'a t -> label:label -> data:'a -> unit

val mem_label : 'a t -> label -> bool

val get_fn_label : 'a t -> Assem.Label.fn_label

val get_data_exn : 'a t -> label:label -> 'a

val get_all_labels : 'a t -> label list 

val map_data : 'a t -> f:('a -> 'b) -> 'b t

val mapi : 'a t -> f:(label:label -> data:'a -> 'b) -> 'b t

val merge_data_exn : 'a t -> 'b t -> f : (label:label -> 'a -> 'b -> 'c) -> 'c t

val remap_labels : 'a t -> f:(label:label -> 'b) -> 'b t

val iter : f:('a -> unit) -> 'a t -> unit

val iteri : f:(label:label -> data:'a -> unit) -> 'a t -> unit

val iter_label : f:(label:label -> unit) -> 'a t -> unit

val iter_forward_edge_srcs : f:(label:label -> unit) -> 'a t -> unit

val reverse_postorder_forward : ?root:label -> 'a t -> label list

val reverse_postorder_backward : ?root:label -> 'a t -> label list

val reverse : 'a t -> 'a t

val remove_node : 'a t -> label -> unit

val remove_unreachable_nodes : 'a t -> unit

module Print :
sig
  val pp_label : label -> string

  val pp_cfg_labels_only : 'a t -> string

  val pp_cfg_graphvis_format : 'a t -> string

  val pp_cfgs_graphvis_format : 'a t list -> string

  val pp_data : 'a t -> data_to_str:('a -> string) -> string
end
