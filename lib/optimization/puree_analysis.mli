(* This module implements an unoptimal form of purity analysis, where it considers all function 
    calls to automatically be impure *)


val puree_analyze : Assem.Quad_With_Temps.program Cfg.t list -> Symbol.t ->  bool   
