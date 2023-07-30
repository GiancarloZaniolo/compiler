(* Library for computing liveness analysis *)
open! Core

module QWT = Assem.Quad_With_Temps
module STIR = Assem.Stack_Temp_Imm_Reg
type reg = string

type line =
  { uses : STIR.t list
  ; defines : STIR.t list
  ; live_out : STIR.t list
  ; move : bool
  ; line_number : int
  }

type program = line list

module Print :
sig
  val pp_line : line -> string

  val pp_program : program -> string
end

val program_of_instrs : QWT.instr list -> program

type allocation = (reg * reg) option
type allocations = allocation list

val live_info_analysis : QWT.program Cfg.t -> program Cfg.t
