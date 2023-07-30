(* File containing code to translate a CFG to SSA, and to destroy SSA *)

module QWT = Assem.Quad_With_Temps
module CFG = Cfg

val create_ssa : QWT.program CFG.t -> unit

val destroy_ssa : QWT.program CFG.t -> unit