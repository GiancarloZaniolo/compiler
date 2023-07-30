(* Implementation of a reverse-dominator tree based on the algorithm presented by Cooper et al. 
 * (Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy. A simple, fast dominance algorithm.
 * Technical Report TR-06-33870, Department of Computer Science, Rice University, 2006.)
 *)

module CFG = Cfg
module VHT = CFG.Vertex.Table

type t
type reverse_t

val idom_exn : reverse_t -> node:CFG.label -> CFG.label option

(* Outputs the post order traversal of the corresponding (forward) dominator tree *)
val post_order : ?root:CFG.label -> t -> CFG.label list

val of_reverse_dt : reverse_t -> t

val compute_reverse_dt : ?root:CFG.label -> 'a CFG.t -> reverse_t

module Print :
sig
  val pp_rdt_graphvis_format : t -> string
end
