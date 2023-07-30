

open Core

include Assem240_intf

(* copy pasted from assem, don't want to put in interface *)
let format_comp_binop = function
  | A.LessThan -> "<"
  | A.LessThanEq -> "<="
  | A.GreaterThan -> ">"
  | A.GreaterThanEq -> ">="
  | A.EqualsTo -> "=="
  | A.NotEqualsTo -> "!="
;;

module Stack_Temp_Imm_Reg = 
struct
  module T = struct
    type t = 
      | Imm of int (* not doing optimizations, and type sizes not defined in implementation, works ok for here *)
      | Temp of Temp.t
      | Reg of risc240_alloc_reg
      | Arg_In_Stack_Idx of int 
      | Arg_Out_Stack_Idx of int
      [@@deriving hash, sexp, compare, equal]
(* not doing optimizations, and type sizes not defined in implementation, works ok *)
    let format_operand = function
      | Imm n -> "$" ^ (Int.to_string n)
      | Temp t -> Temp.name t
      | Reg r -> show_risc240_alloc_reg r
      | Arg_In_Stack_Idx i -> "idx:" ^ (Int.to_string i)
      | Arg_Out_Stack_Idx i -> "idx:" ^ (Int.to_string i)
  end
  include T
  include Hashable.Make(T)
  (* include Comparable.Make(T) *)
end

module Stack_Imm_Reg = 
struct
  module T = struct
    type t =
      | Imm of int
      | Reg of risc240_alloc_reg
      | Stack_Offset of int
      [@@deriving hash, sexp, compare, equal]

    let format_operand = function
      | Imm n -> format_hex_16 n
      | Reg r -> show_risc240_alloc_reg r
      | Stack_Offset i -> "Stk:rsp+" ^ (Int.to_string i)
  end
  include T
  include Hashable.Make(T)
end


module Make_Nonfinal (Operand : Hashable_Operand) : RISC240_Assem with type operand := Operand.t = 
struct
  type operand = Operand.t
  module Operand_hashtbl = Operand.Table

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

  let format = function 
    | Binop binop ->
      sprintf
        "\t%s <-- %s %s %s"
        (Operand.format_operand binop.dest)
        (Operand.format_operand binop.lhs)
        (format_op_nonfinal binop.op)
        (Operand.format_operand binop.rhs)
    | Mov mv -> 
      sprintf
      "\t%s <-- %s"
      (Operand.format_operand mv.dest)
      (Operand.format_operand mv.src)
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
        (A.format_sized_temp dest) 
        (Label.format_fn_label c.fn_label)
    | None -> 
      sprintf 
        "\tvoid <-- call %s"
        (Label.format_fn_label c.fn_label))
    | Label l -> Label.format_label l
    | Return (Some op) -> sprintf "\tret %s" (Operand.format_operand op)
    | Return (None) -> sprintf "\tret"
    | STOP -> "\tSTOP"
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
    | Inc_RSP i -> sprintf "\trsp += %d" i
    | Directive d -> d
    | Comment comment -> sprintf "/* %s */" comment

  (* need different formatting functions because code is fundamentally different *)
  let pp_program = Print_utils.pp_list ~sep:"\n" ~f:format
end

module RISC240_With_Temps = Make_Nonfinal(Stack_Temp_Imm_Reg)
module RISC240_Regalloc = Make_Nonfinal(Stack_Imm_Reg)



module RISC240 = 
struct 
  type risc240_threeop_cmd = 
  | ADD | AND | OR | SLL | SLT | SRA | SRL | SRLI | SUB | XOR [@@deriving show { with_path = false }]

  type risc240_threeop_imm_cmd =
  | ADDI | LW | SLLI | SLTI | SRAI | SRLI | SW [@@deriving show { with_path = false }]

  type risc240_twoop_cmd = 
  | MV | NOT [@@deriving show { with_path = false }]

  type risc240_branch_cmd = 
  | BRA | BRC | BRN | BRNZ | BRV | BRZ [@@deriving show { with_path = false }]

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
  (* maybe comment *)
  
  type program = instr list

  let format = function
  | Threeop t -> 
    sprintf "\t%s %s, %s, %s"
      (show_risc240_threeop_cmd t.op)
      (show_risc240_reg t.dest)
      (show_risc240_reg t.lhs)
      (show_risc240_reg t.rhs)
  | Threeop_imm t -> 
    sprintf "\t%s %s, %s, %s"
      (show_risc240_threeop_imm_cmd t.op)
      (show_risc240_reg t.dest)
      (show_risc240_reg t.lhs)
      (format_hex_16 t.imm)
  | Twoop t ->
    sprintf "\t%s %s, %s"
      (show_risc240_twoop_cmd t.op)
      (show_risc240_reg t.dest)
      (show_risc240_reg t.src)
  | LI l -> 
    sprintf "\tLI %s, %s"
      (show_risc240_reg l.dest)
      (format_hex_16 l.imm)
  | Local_label l -> 
    "_" ^ (String.chop_prefix_if_exists ~prefix:"." (Symbol.name l))
  | Fn_label l -> 
    Symbol.name l
  | Branch b -> 
    sprintf "\t%s %s"
    (show_risc240_branch_cmd b.op)
    (match b.dest with
    | Addr a -> format_hex_16 a
    | Label l -> (match String.chop_prefix ~prefix:"." (Symbol.name l) with
      | Some l_chop -> "_" ^ l_chop
      | None -> Symbol.name l))
  | STOP -> "\tSTOP"
  | Directive d -> d
end


(* trans to assem240 will already turn shifts, mults, and divs into function calls *)

(* trans to assem240 will already turn shifts, mults, and divs into function calls *)
