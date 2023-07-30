(* Defines the signatures for operands and quad assembly representations. *)

open Core

(* Need this so that we can access the type constructors outside of the file *)
type x86_operand_size = S_32 | S_64
  [@@deriving compare, sexp, hash, equal, show { with_path = false }]

let format_size = function
  | S_32 -> "32"
  | S_64 -> "64"

type x86_addr_mode_scale = SC_1 | SC_2 | SC_4 | SC_8 [@@deriving hash, sexp, compare, equal]

let addr_mode_scale_to_int64 = function
  | SC_1 -> Int64.of_int 1 
  | SC_2 -> Int64.of_int 2 
  | SC_4 -> Int64.of_int 4 
  | SC_8 -> Int64.of_int 8 

let format_scale scale = addr_mode_scale_to_int64 scale |> Int64.to_string

let int_to_addr_mode_scale = function
  | 1 -> Some SC_1 | 2 -> Some SC_2 | 4 -> Some SC_4 | 8 -> Some SC_8 | _ -> None

(* The order of the constructors here matters because we want to prioritize caller-save regs *)
type x86_reg_64 = 
  | RDI | RSI | RDX | RCX | R8 | R9 | RAX | R10 | R11 (* Caller-save registers *)
  | RBX | R12 | R13 | R14 | R15 | RSP | RBP (* Callee-save registers *)
  [@@deriving hash, compare, sexp, equal, enumerate, show { with_path = false } ]

let x86_arg_regs = [ RDI ; RSI ; RDX ; RCX ; R8 ; R9 ]
let x86_caller_saved_regs = List.append x86_arg_regs [ RAX ; R10 ; R11 ]
let x86_callee_saved_regs = [ RBP ; RBX ; R12 ; R13 ; R14 ; R15 ]
let stack_reserve_reg = R15
let mem_reserve_reg = R14

type sized_temp = { size : (x86_operand_size [@compare.ignore] [@equal.ignore]) ; temp : Temp.t }
  [@@deriving hash, compare, sexp, equal]

let format_sized_temp sized_temp =
  sprintf
    "(%s):%s"
    (format_size sized_temp.size)
    (Temp.name sized_temp.temp)

type sized_reg = { size : x86_operand_size ; reg : x86_reg_64 }
  [@@deriving hash, compare, sexp, equal]
let format_sized_reg sized_reg =
  sprintf
  "(%s):%s"
  (format_size sized_reg.size)
  (show_x86_reg_64 sized_reg.reg)

type sized_st_idx = { size : x86_operand_size ; idx : int } [@@deriving hash, compare, sexp, equal]
let format_sized_st_idx sized_st_index =
  sprintf 
  "%s idx:%d"
  (show_x86_operand_size sized_st_index.size) sized_st_index.idx

let stack_reserve_reg_32 : sized_reg = { reg = stack_reserve_reg ; size = S_32 }
let stack_reserve_reg_64 : sized_reg = { reg = stack_reserve_reg ; size = S_64 }

let mem_reserve_reg_64 : sized_reg = { reg = mem_reserve_reg ; size = S_64 }
let word_size = 8

let arith_int = 8
let mem_int = 12

type quad_arith_binop = 
  | Add | Sub | Mul | Div | Mod | LShift | RShift | RShift_unsigned | BWXor | BWAnd | BWOr
  [@@deriving hash, sexp, compare, equal]
type quad_comp_binop =
  | LessThan | LessThanEq | GreaterThan | GreaterThanEq | EqualsTo | NotEqualsTo
type quad_unop = CDQ | MOVSXD | LEA
type quad_except = Arith | Mem
type 'a quad_binop = { op : quad_arith_binop ; dest : 'a ; lhs : 'a ; rhs : 'a }
module Label =
struct 
  type fn_label = 
    { name : Symbol.t ; param_temps : sized_temp list ; ret_size_opt : x86_operand_size option }
    [@@deriving hash, sexp, compare, equal]
  module T = 
  struct
    type t =
      Local_label of Local_label.t | Fn_label of fn_label | ENTRY_LABEL | EXIT_LABEL | MEM_LABEL
      | ARITH_LABEL
      [@@deriving hash, sexp, compare, equal]
  end
  include T
  include Hashable.Make(T)

  let format_fn_label ?(fn_args=true) fn_label = 
    let args_str =
      if fn_args then
        sprintf "(%s)" (Print_utils.pp_list ~f:format_sized_temp fn_label.param_temps)
      else ""
    in
    sprintf "%s%s" (Symbol.name fn_label.name) (args_str)
       
  let format_label ?(fn_args=true) = function
    | Local_label label -> Local_label.name label
    | Fn_label fn -> format_fn_label fn ~fn_args
    | ENTRY_LABEL -> ".ENTRY"
    | EXIT_LABEL -> ".EXIT"
    | MEM_LABEL -> ".MEM"
    | ARITH_LABEL -> ".ARITH"
  
  let lbl_to_int int_label =
    match int_label with
    | ARITH_LABEL -> arith_int
    | MEM_LABEL -> mem_int
    | (Local_label _ | Fn_label _ | ENTRY_LABEL | EXIT_LABEL) ->
      sprintf "Can't get an interrupt code for non-interrupt label: `%s`"
        (format_label int_label)
      |> failwith
end

type call = { fn_label : Label.fn_label ; dest : sized_temp option }
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

module type Three_Addr_Assem =
sig
  type operand
  module Operand_hashtbl : Hashtbl.S with type key := operand

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
        ; srcs : Label.Hash_set.t Operand_hashtbl.t }
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
  
  val format_arith_binop : quad_arith_binop -> string
  val format : instr -> string

  val pp_program : program -> string
end