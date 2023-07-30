(* Module for translating quad assembly to control-flow graphs and back *)

module QWT = Assem.Quad_With_Temps

val quad_to_cfg : QWT.program -> QWT.program Cfg.t list

val list_cfg_to_list : 'a list Cfg.t -> 'a list

val list_cfg_program_to_list : 'a list Cfg.program -> 'a list
