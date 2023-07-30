
open Core 

module A = Assem
module Label = A.Label

(* 1 = arith, 2 = mem, 3 = overflow, 0 = normal exec? *)

type risc240_reg = R0 | R1 | R2 | R3 | R4 | R5 | R6 | R7 
  [@@deriving hash, sexp, compare, equal, show { with_path = false }]

type risc240_alloc_reg = Reg1 | Reg2 
  [@@deriving hash, sexp, compare, equal, enumerate, show { with_path = false }]

let reg1_upper = R1
let reg1_lower = R2
let reg2_upper = R3
let reg2_lower = R4
let mem_reg1 = R5 (* upper when relevant *)
let mem_reg2 = R6 (* lower when relevant *)
let rsp = R7
let arith_code = 1
let mem_code = 2
let s_overflow_code = 3
let no_error = 0


let risc240_arg_regs = [ Reg1 ; Reg2 ]
let risc240_caller_saved_regs = [ Reg1 ; Reg2 ]
let risc240_callee_saved_regs = [ ]

let word_size = 4
let lower_offset = 2

let max_16_bit = 65535

type risc240_binop = 
  | ADD_p | AND_p | OR_p | SUB_p | XOR_p
let format_op_nonfinal = function
  | ADD_p -> "+"
  | SUB_p -> "-"
  | AND_p -> "&"
  | OR_p -> "|"
  | XOR_p -> "^"

type risc240_except = Arith | Mem | Stack_overflow

let format_hex_16 n = 
  if not (Int.equal (Int.(shift_right) n 16) 0) then
    failwith "expected size 16 argument to be size 16"
  else 
    sprintf "$%x" n

(* Yoink label type from assem_intf *)

(* yoink function call type from label *)

(* This is copy pasted from Assem, I don't know if we want to put it in the interface *)
module type Operand_T =
sig
  type t [@@deriving hash, sexp, compare]

  (* functions that format assembly output *)
  val format_operand : t -> string
end

module type Hashable_Operand =
sig
  include Operand_T
  include Hashable.S with type t := t   
end

module type RISC240_Assem = 
sig 
  type operand
  module Operand_hashtbl : Hashtbl.S with type key := operand

  type instr = 
    | Binop of 
      { op : risc240_binop
      ; lhs : operand
      ; rhs : operand
      ; dest : operand }
    | Mov of
      { dest : operand
      ; src : operand 
      }
    | If of
      { op : A.quad_comp_binop
      ; lhs : operand
      ; rhs : operand
      ; if_true : Label.t 
      ; if_false : Label.t 
      }
    | Call of A.call (*needed but deleted in conv trans*)
    | Goto of Label.t
    | Label of Label.t
    | Return of operand option (*needed but deleted in conv trans*)
    | STOP 
    | Mem_read of
      { dest : operand
      ; src : operand
      ; imm : int
      }
    | Mem_write of
      { dest : operand 
      ; src : operand 
      ; imm : int }
    | Inc_RSP of int
    | Directive of string
    | Comment of string 

  type program = instr list

  (* val format_risc240_binop : risc240_binop -> string *)
  val format : instr -> string

  val pp_program : program -> string

end

