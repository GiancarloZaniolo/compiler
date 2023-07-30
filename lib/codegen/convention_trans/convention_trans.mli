(* Three-address intermediate translation step to add in x86-64 calling conventions. *)

val translate : Assem.Quad_With_Temps.program Cfg.t -> Assem.Quad_With_Temps.program Cfg.t