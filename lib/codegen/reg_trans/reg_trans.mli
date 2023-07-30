(* Translation function for mapping infinite-temp quad assembly to register-allocated quad 
 * assembly. *)
module QWT = Assem.Quad_With_Temps
module QR = Assem.Quad_Regalloc

val translate_to_quad_regalloc :
    ?coalesce:bool -> ?regalloc_cfg:bool -> QWT.instr list -> QWT.program Cfg.program
    -> QR.instr list
