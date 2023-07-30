(* Implementation of per-node dataflow frontier calculation based on the paper by Cooper et al.
 * (Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy. A simple, fast dominance algorithm.
 * Technical Report TR-06-33870, Department of Computer Science, Rice University, 2006.)
 *)

type t

val frontier_exn : t -> Cfg.label -> Cfg.label List.t

val compute : 'a Cfg.t -> Dominator_tree.reverse_t -> t

module Print :
sig
  val pp_dfg_graphvis_format : t -> string
end
