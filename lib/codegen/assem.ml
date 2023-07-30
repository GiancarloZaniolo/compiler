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
 *)

open Core

include Assem_intf

let format_reg_64_as_32 reg = "%" ^ 
(match reg with 
  | RDI -> "EDI"
  | RSI -> "ESI"
  | RDX -> "EDX"
  | RCX -> "ECX"
  | R8 -> "R8D"
  | R9 -> "R9D"
  | RAX -> "EAX"
  | R10 -> "R10D"
  | R11 -> "R11D"
  | RBX -> "EBX"
  | R12 -> "R12D"
  | R13 -> "R13D"
  | R14 -> "R14D"
  | R15 -> "R15D"
  | RSP -> "ESP"
  | RBP -> "EBP")
let format_x86_reg_64 reg = "%" ^ show_x86_reg_64 reg

(* We make the operands hashable for graph construction in regalloc *)
module Stack_Temp_Imm_Reg =
struct
  module T = struct
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

    let format_operand = function
      | Imm32 n -> "(32):$" ^ Int32.to_string n
      | Imm64 n -> "(64):$" ^ Int64.to_string n
      | Temp t -> format_sized_temp t
      | Reg r -> format_sized_reg r
      | Arg_In_Stack_Idx i -> 
        sprintf "%s %%arg_in_%d" (show_x86_operand_size i.size) (i.idx + (List.length x86_arg_regs))
      | Arg_Out_Stack_Idx i -> 
        sprintf "%s %%arg_out_%d" (show_x86_operand_size i.size) (i.idx + (List.length x86_arg_regs))
      | Addr_mode exp ->
        sprintf "%s(%s, %s, %s)"
          (Int32.to_string exp.disp)
          (format_sized_temp exp.base)
          (format_sized_temp exp.index)
          (format_scale exp.scale)
    ;;

  end
  include T
  include Hashable.Make(T)
  include Comparable.Make(T)
  let resize_64 s = (match s with
    | Reg r -> Reg { reg = r.reg ; size = S_64 } 
    | Temp t -> Temp { temp = t.temp ; size = S_64 }
    | Arg_In_Stack_Idx s -> Arg_In_Stack_Idx { idx = s.idx ; size = S_64 }
    | Arg_Out_Stack_Idx s -> Arg_Out_Stack_Idx { idx = s.idx ; size = S_64 }
    | Imm32 _ | Imm64 _ | Addr_mode _ -> s)
  
  let size_of = function
    | Reg r -> r.size
    | Temp t -> t.size
    | Arg_In_Stack_Idx s
    | Arg_Out_Stack_Idx s -> s.size
    | Imm32 _ -> S_32
    | Imm64 _ -> S_64
    | Addr_mode _ -> S_64 (* TODO: this depends on what the expression is used for *)

  let reg_to_op_64 reg = Reg { reg ; size = S_64 }
end

module Stack_Imm_Reg =
struct
  module T = struct
    type t =
      | Imm32 of Int32.t
      | Imm64 of Int64.t
      | Reg of sized_reg
      | Stack_Offset of sized_st_idx 
      | Addr_mode of
          { disp : Int32.t
          ; base : t 
          ; index : t
          ; scale : x86_addr_mode_scale
          }
      [@@deriving hash, sexp, compare, equal]

    let rec format_operand = function
      | Imm32 n -> sprintf "$%lu" (Int32.to_int32 n)
      | Imm64 n -> sprintf "$%Lu" (Int64.to_int64 n)
      | Stack_Offset i -> (Int.to_string i.idx) ^ "(%rsp)"
      | Reg r -> (match r.size with 
        | S_32 -> format_reg_64_as_32 r.reg 
        | S_64 -> format_x86_reg_64 r.reg)
      | Addr_mode exp ->
        sprintf "%s(%s, %s, %s)"
          (Int32.to_string exp.disp)
          (format_operand exp.base)
          (format_operand exp.index)
          (format_scale exp.scale)
    ;;
    let operand_size = function
      | Imm32 _ -> S_32
      | Imm64 _ -> S_64
      | Stack_Offset i -> i.size
      | Reg r -> r.size
      | Addr_mode _ -> S_64 (* TODO: This depends on what the expression is for *)

    let reg_to_op_64 reg = Reg { reg ; size = S_64 }
  end
  include T
  include Hashable.Make(T)
end

(* Functor used to create quad assembly with a certain operand type *)
module Make_Quad (Operand : Hashable_Operand) : Three_Addr_Assem with type operand := Operand.t =
struct
  type operand = Operand.t
  module Operand_hashtbl = Operand.Table
  type instr =
    | Binop of operand quad_binop 
    | Unop of 
        { op : quad_unop
        ; dest : operand
        ; src : operand
        }
    | Mov of
        { dest : operand
        ; src : operand
        }
    | Phi of
        { dest : operand
        ; srcs : Label.Hash_set.t Operand_hashtbl.t  }
    | If of
        { op : quad_comp_binop
        ; lhs : operand
        ; rhs : operand
        ; if_true : Label.t
        ; if_false : Label.t 
        }
    | Call of call
    | Goto of Label.t
    | Label of Label.t
    | Return of operand option
    | Mem_read of
        { dest : operand 
        ; src : operand 
        }
    | Mem_write of
        { dest : operand 
        ; src : operand 
        }
    | Directive of string
    | Comment of string

  type program = instr list

  let format_arith_binop = function
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Mod -> "%"
    | LShift -> "<<"
    | RShift -> ">>s"
    | RShift_unsigned -> ">>u"
    | BWXor -> "^"
    | BWAnd -> "&"
    | BWOr -> "|"
  let format_comp_binop = function
    | LessThan -> "<"
    | LessThanEq -> "<="
    | GreaterThan -> ">"
    | GreaterThanEq -> ">="
    | EqualsTo -> "=="
    | NotEqualsTo -> "!="
  ;;

  let format_unoperand = function
    | CDQ -> "CDQ"
    | MOVSXD -> "MOVSXD"
    | LEA -> "LEA"
  ;;

  let format_phi_src (op, verts) = 
    sprintf 
      "(%s,(%s))"
      (Operand.format_operand op)
      (Print_utils.pp_list (Hash_set.to_list verts) ~sep:"," ~f:(Label.format_label))

  let format = function
    | Binop binop ->
      sprintf
        "\t%s <-- %s %s %s"
        (Operand.format_operand binop.dest)
        (Operand.format_operand binop.lhs)
        (format_arith_binop binop.op)
        (Operand.format_operand binop.rhs)
    | Unop unop -> 
      sprintf
        "\t%s <-- %s %s"
        (Operand.format_operand unop.dest)
        (format_unoperand unop.op)
        (Operand.format_operand unop.src)
    | Mov mv -> 
      sprintf
        "\t%s <-- %s"
        (Operand.format_operand mv.dest)
        (Operand.format_operand mv.src)
    | Phi phi -> 
      sprintf 
        "\t%s <- phi [%s]"
        (Operand.format_operand phi.dest)
        (Operand_hashtbl.to_alist phi.srcs |> Print_utils.pp_list ~f:(format_phi_src))
    | If i -> 
      sprintf 
        "\tif (%s %s %s) %s %s" 
        (Operand.format_operand i.lhs)
        (format_comp_binop i.op)
        (Operand.format_operand i.rhs)
        (Label.format_label i.if_true)
        (Label.format_label i.if_false)
    | Goto lbl -> sprintf "\tgoto %s" (Label.format_label lbl)
    | Call c -> (match c.dest with
      | Some dest -> 
        sprintf 
          "\t%s <-- call %s"
          (format_sized_temp dest) 
          (Label.format_fn_label c.fn_label)
      | None -> 
        sprintf 
          "\tvoid <-- call %s"
          (Label.format_fn_label c.fn_label))
    | Label l -> sprintf "%s" (Label.format_label l)
    | Return (Some op) -> sprintf "\tret %s" (Operand.format_operand op)
    | Return (None) -> sprintf "\tret"
    | Mem_read m -> 
      sprintf
        "\t%s <-- *(%s)\n"
        (Operand.format_operand m.dest)
        (Operand.format_operand m.src)
    | Mem_write m -> 
      sprintf
        "\t*(%s) <-- %s\n"
        (Operand.format_operand m.dest)
        (Operand.format_operand m.src)
    | Directive dir -> dir
    | Comment comment -> sprintf "/* %s */" comment
  ;;

  let pp_program = Print_utils.pp_list ~sep:"\n" ~f:format
end

module X86_Assem =
struct
  module SIR = Stack_Imm_Reg
  (* The purpose of the x84 data structure is to replicate output assembly as closely as possible *)

  type two_operand_op =
    ADD | SUB | IMUL | MOV | AND | XOR | OR | SAL | SAR | SHR | CMP | MOVSXD | LEA
    [@@deriving show { with_path = false }]
  type one_operand_op = IDIV | POPQ | PUSHQ [@@deriving show { with_path = false }]
  type zero_operand_op = CDQ [@@deriving show { with_path = false }]
  type jmp_op = JMP | JL | JLE | JG | JGE | JE | JNE [@@deriving show { with_path = false }]

  type x86_instr = 
  | TwoOp of { op : two_operand_op; src : SIR.t ; dest : SIR.t }
  | OneOp of { op : one_operand_op; operand : SIR.t }
  | ZeroOp of zero_operand_op
  | JmpOp of { op : jmp_op; label : Symbol.t }
  | Local_label of Symbol.t
  | Fn_label of Symbol.t
  | Call of Symbol.t
  | Interrupt of int
  | Return
  | Mem_read of { src : SIR.t ; dest : sized_reg }
  | Mem_write of { src : SIR.t ; dest : SIR.t }
  | Directive of string

  type program = x86_instr list

  let format_two_operand_op (op : SIR.t) = 
    (match SIR.operand_size op with 
    | S_32 -> fun a -> (show_two_operand_op a) ^ "L" 
    | S_64 -> fun a -> (show_two_operand_op a) ^ "Q")
  let format_one_operand_op (op : SIR.t) = 
    (match SIR.operand_size op with 
    | S_32 -> fun a -> (show_one_operand_op a) ^ "L" 
    | S_64 -> fun a -> (show_one_operand_op a) ^ "Q")
  let format_zero_operand_op = show_zero_operand_op
  let format_jmp_op = show_jmp_op

  let format = function
  | TwoOp twoOp ->
    (match twoOp.op with 
    | MOVSXD -> sprintf "\tMOVSXD %s, %s"
      (SIR.format_operand twoOp.src)
      (SIR.format_operand twoOp.dest)
    | _ -> sprintf "\t%s %s, %s" 
      (format_two_operand_op twoOp.src twoOp.op) 
      (SIR.format_operand twoOp.src)
      (SIR.format_operand twoOp.dest))
  | OneOp oneOp -> 
    sprintf "\t%s %s" (format_one_operand_op oneOp.operand oneOp.op) (SIR.format_operand oneOp.operand)
  | ZeroOp zeroOp -> 
    sprintf "\t%s" (format_zero_operand_op zeroOp)
  | JmpOp jmpOp -> 
    sprintf "\t%s %s"
      (format_jmp_op jmpOp.op)
      (Symbol.name jmpOp.label)
  | Local_label label -> sprintf "%s:" (Symbol.name label)
  | Fn_label label -> sprintf ".globl %s\n%s:" (Symbol.name label) (Symbol.name label)
  | Call fn_name -> sprintf "\tCALL %s" (Symbol.name fn_name)
  | Interrupt i -> 
    if i = 0 then "\tMOV $0, %RAX\n\tIDIV %RAX" 
    else "\tMOV $12, %EDI\n\tcall raise"
  | Return -> "\tRET"
  | Mem_read m -> 
      sprintf "\t%s (%s), %s" 
      (format_two_operand_op (SIR.Reg m.dest) MOV)
      (SIR.format_operand (m.src))
      (SIR.format_operand (SIR.Reg m.dest)) 
  | Mem_write m -> 
      sprintf "\t%s %s, (%s)" 
      (format_two_operand_op m.src MOV)
      (SIR.format_operand m.src) 
      (SIR.format_operand m.dest) 
  | Directive dir -> dir
end

(* Creates quad assembly module with temp/pre-defined register operand type *)
module Quad_With_Temps = Make_Quad(Stack_Temp_Imm_Reg)
(* Creates quad assembly module with register/stack position operand type *)
module Quad_Regalloc = Make_Quad(Stack_Imm_Reg)
