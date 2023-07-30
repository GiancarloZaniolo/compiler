(* L4 Compiler
 * Assembly language
 * Author: Kaustuv Chaudhuri <kaustuv+@andrew.cmu.edu>
 * Modified By: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Elan Biswas (elanb)
 *
 * Currently just a pseudo language with 3-operand
 * instructions and arbitrarily many temps
 *
 *)

open Core

include module type of Assem_intf

module Stack_Temp_Imm_Reg : 
sig
    type t =
        | Imm32 of Int32.t
        | Imm64 of Int64.t
        | Reg of sized_reg
        | Temp of sized_temp
        (* Represents the current function's (i + 6)th argument stack index *)
        | Arg_In_Stack_Idx of sized_st_idx
        (* Represents the callee's (i + 6th) argument stack index *)
        | Arg_Out_Stack_Idx of sized_st_idx
        | Addr_mode of
            { disp : Int32.t
            ; base : sized_temp
            ; index : sized_temp
            ; scale : x86_addr_mode_scale
            }
        [@@deriving hash, sexp, compare, equal]

    val format_operand : t -> string

    val resize_64 : t -> t
    
    val size_of : t -> x86_operand_size

    val reg_to_op_64 : x86_reg_64 -> t
    
    include Hashable.S with type t := t
    include Comparable.S with type t := t 
end

(* We make the operands hashable for graph construction in regalloc *)
module Stack_Imm_Reg :
sig
    type t =
        | Imm32 of Int32.t
        | Imm64 of Int64.t
        | Reg of sized_reg
        | Stack_Offset of sized_st_idx (* Represents the distance in bytes from %rsp to the operand *)
        | Addr_mode of
            { disp : Int32.t
            ; base : t 
            ; index : t
            ; scale : x86_addr_mode_scale
            }
        [@@deriving hash, sexp, compare, equal]

    val format_operand : t -> string

    val operand_size : t -> x86_operand_size

    val reg_to_op_64 : x86_reg_64 -> t

    include Hashable.S with type t := t
end

module Quad_With_Temps : Three_Addr_Assem with type operand := Stack_Temp_Imm_Reg.t
module Quad_Regalloc : Three_Addr_Assem with type operand := Stack_Imm_Reg.t

module X86_Assem :
sig
    (* Operations *)
    type two_operand_op =
        ADD | SUB | IMUL | MOV | AND | XOR | OR | SAL | SAR | SHR | CMP | MOVSXD | LEA
    type one_operand_op = IDIV | POPQ | PUSHQ
    type zero_operand_op = CDQ
    type jmp_op = JMP | JL | JLE | JG | JGE | JE | JNE


    type x86_instr = 
    | TwoOp of {op : two_operand_op; src : Stack_Imm_Reg.t ; dest : Stack_Imm_Reg.t}
    | OneOp of {op : one_operand_op; operand : Stack_Imm_Reg.t}
    | ZeroOp of zero_operand_op
    | JmpOp of {op : jmp_op; label : Symbol.t}
    | Local_label of Symbol.t 
    | Fn_label of Symbol.t
    | Call of Symbol.t
    | Interrupt of int
    | Return
    | Mem_read of { src : Stack_Imm_Reg.t ; dest : sized_reg }
    | Mem_write of { src : Stack_Imm_Reg.t ; dest : Stack_Imm_Reg.t }
    | Directive of string
    type program = x86_instr list
  
    (* Used to create x86 lines string *)
    val format : x86_instr -> string
end

val format_reg_64_as_32 : x86_reg_64 -> string
val format_x86_reg_64 : x86_reg_64 -> string
