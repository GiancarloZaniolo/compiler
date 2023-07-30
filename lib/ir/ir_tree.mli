(* Interface for the IR Tree.
 * Author: Giancarlo Zaniolo (gzaniolo)
 *)

open Core


type binop_pure = 
  | Plus
  | Minus
  | Times
  | BitwiseAnd
  | BitwiseXor
  | BitwiseOr 

type binop_impure = 
  | Divided_by
  | Modulo
  | LShift
  | RShift

type binop_comp = 
  | LessThan
  | LessThanEq
  | GreaterThan
  | GreaterThanEq
  | EqualsTo
  | NotEqualsTo

type exp_pure = 
  | Const32 of Int32.t
  | Const64 of Int64.t
  | Temp of Assem.sized_temp
  | Binop_pure of { lhs : exp_pure; op : binop_pure; rhs : exp_pure }

type label = Local_label.t

type command = 
  | Move of { src : exp_pure; dest : Assem.sized_temp }
  | Binop_impure of { lhs : exp_pure; op : binop_impure; rhs : exp_pure; dest : Assem.sized_temp }
  | Fn_Call of { name : Symbol.t ; arg_list : exp_pure list ; dest : Assem.sized_temp option }
  | If of { lhs : exp_pure; op : binop_comp; rhs : exp_pure; tru : label; fls : label }
  | Goto of label
  | Label of label
  | Fn_Label of Assem.Label.fn_label
  | Alloc of { typ_size : int ; dest : Assem.sized_temp }
  | Alloc_arr of { typ_size : int ; count : exp_pure ; dest : Assem.sized_temp }
  | Field_acc_addr of { struct_ : exp_pure ; offset : int ; dest : Assem.sized_temp }
  | Arr_acc_addr of { arr : exp_pure ; typ_size : int ; index : exp_pure ; dest : Assem.sized_temp }
  | Unchecked_read of { src : exp_pure ; dest : Assem.sized_temp }
  | Checked_read of { src : exp_pure ; dest : Assem.sized_temp }
  | Unchecked_write of { src : exp_pure ; dest : Assem.sized_temp } 
  | Checked_write of { src : exp_pure ; dest : Assem.sized_temp }
  | Return of exp_pure option

type program = command list


module Print : sig
  val pp_exp_pure : exp_pure -> string
  val pp_command : command -> string
  val pp_program : program -> string
end