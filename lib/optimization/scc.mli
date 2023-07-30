(* Module which implementes Sparse Conditional Copy Propagation optimization *)

val scc_optimize : Assem.Quad_With_Temps.program Cfg.t -> Assem.Quad_With_Temps.program Cfg.t 
