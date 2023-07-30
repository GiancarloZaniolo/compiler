(* Copy propagation on SSA *)

val ssa_copy_prop : Assem.Quad_With_Temps.program Cfg.t -> Assem.Quad_With_Temps.program Cfg.t