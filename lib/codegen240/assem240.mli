
open Core

include module type of Assem240_intf

module Stack_Temp_Imm_Reg : 
sig
  type t = 
    | Imm of int (* not doing optimizations, and type sizes not defined in implementation, works ok for here *)
    | Temp of Temp.t
    | Reg of risc240_alloc_reg
    | Arg_In_Stack_Idx of int 
    | Arg_Out_Stack_Idx of int
    [@@deriving hash, sexp, compare, equal]

  val format_operand : t -> string

  include Hashable.S with type t := t
  (* include Comparable.S with type t := t *)
end

module Stack_Imm_Reg : 
sig
  type t =
    | Imm of int
    | Reg of risc240_alloc_reg
    | Stack_Offset of int
    [@@deriving hash, sexp, compare, equal]

  val format_operand : t -> string

  include Hashable.S with type t := t
end

(* TODO: other two assems *)
module RISC240_With_Temps : RISC240_Assem with type operand := Stack_Temp_Imm_Reg.t
module RISC240_Regalloc : RISC240_Assem with type operand := Stack_Imm_Reg.t

module RISC240 : 
sig 
  type risc240_threeop_cmd = 
  | ADD | AND | OR | SLL | SLT | SRA | SRL | SRLI | SUB | XOR [@@deriving show]
  
  type risc240_threeop_imm_cmd =
  | ADDI | LW | SLLI | SLTI | SRAI | SRLI | SW [@@deriving show]
  
  type risc240_twoop_cmd = 
  | MV | NOT [@@deriving show]
  
  type risc240_branch_cmd = 
  | BRA | BRC | BRN | BRNZ | BRV | BRZ [@@deriving show]

  type goto_dest = Addr of int | Label of Symbol.t

  type instr = 
  | Threeop of 
    { op : risc240_threeop_cmd 
    ; dest : risc240_reg 
    ; lhs : risc240_reg 
    ; rhs : risc240_reg
    }
  | Threeop_imm of
    { op : risc240_threeop_imm_cmd
    ; dest : risc240_reg
    ; lhs : risc240_reg
    ; imm : int
    }
  | Twoop of
    { op : risc240_twoop_cmd 
    ; dest : risc240_reg
    ; src : risc240_reg 
    }
  | LI of 
    { dest : risc240_reg 
    ; imm : int
    }
  | Local_label of Symbol.t
  | Fn_label of Symbol.t
  | Branch of { op : risc240_branch_cmd ; dest : goto_dest }
  | STOP
  | Directive of string
  (* Maybe comment *)
  
  type program = instr list

  val format : instr -> string 
end