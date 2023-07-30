
open! Core

module RWT = Assem240.RISC240_With_Temps
module STIR240 = Assem240.Stack_Temp_Imm_Reg
type reg = string

type line =
  { uses : STIR240.t list
  ; defines : STIR240.t list
  ; live_out : STIR240.t list
  ; move : bool
  ; line_number : int
  }

type program = line list

module Print :
sig
  val pp_line : line -> string

  val pp_program : program -> string
end

val program_of_instrs : RWT.instr list -> program

type allocation = (reg * reg) option
type allocations = allocation list

val live_info_analysis : RWT.program Cfg.t -> program Cfg.t