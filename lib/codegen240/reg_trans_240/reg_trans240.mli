

val translate_to_RISC240_regalloc : 
  ?coalesce:bool -> Assem240.RISC240_With_Temps.instr list ->  
  Assem240.RISC240_With_Temps.instr list Cfg.program -> Assem240.RISC240_Regalloc.instr list