(* L4 Compiler
 * IR Tree Implementation
 * Author: Giancarlo Zaniolo (gzaniolo)
 *)

open Core


(* ---------------------------------- IR TREE TYPE DEFINITIONS ---------------------------------- *)
 
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
  | Binop_pure of {lhs : exp_pure; op : binop_pure; rhs : exp_pure}

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
 
(* -------------------------------- END IR TREE TYPE DEFINITIONS -------------------------------- *)
(* ---------------------------------   BEGIN PRINT FUNCTIONS   ---------------------------------- *)
 
module Print = struct
  let pp_binop_pure = function
    | Plus -> "+"
    | Minus -> "-"
    | Times -> "*"
    | BitwiseAnd -> "&"
    | BitwiseXor -> "^"
    | BitwiseOr  -> "|"

  let pp_binop_impure = function
    | Divided_by -> "/"
    | Modulo -> "%"
    | LShift -> "<<"
    | RShift -> ">>"

  let pp_exp_binop_comp = function
    | LessThan -> "<"
    | LessThanEq -> "<="
    | GreaterThan -> ">"
    | GreaterThanEq -> ">="
    | EqualsTo -> "=="
    | NotEqualsTo -> "!="

  let pp_label = Local_label.name

  let rec pp_exp_pure = function
    | Const32 i -> Int32.to_string i
    | Const64 i ->  Int64.to_string i
    | Temp s -> Assem.format_sized_temp s
    | Binop_pure b -> 
        sprintf "(%s) %s (%s)" (pp_exp_pure b.lhs) (pp_binop_pure b.op) (pp_exp_pure b.rhs)

  let pp_command = function
    | Move m -> sprintf "\t%s <- %s\n" (pp_exp_pure (Temp m.dest)) (pp_exp_pure m.src)
    | Binop_impure b ->
      sprintf "\t%s <- (%s) %s (%s)\n"
        (pp_exp_pure (Temp b.dest))
        (pp_exp_pure b.lhs) 
        (pp_binop_impure b.op) (pp_exp_pure b.rhs)
    | If i ->
      sprintf "\tif (%s %s %s) then %s else %s\n"
        (pp_exp_pure i.lhs) 
        (pp_exp_binop_comp i.op)
        (pp_exp_pure i.rhs)
        (pp_label i.tru)
        (pp_label i.fls)
    | Goto g -> sprintf "\tgoto: %s\n" (pp_label g)
    | Label l -> pp_label l ^ "\n"
    | Return (Some r) -> sprintf "\treturn %s\n" (pp_exp_pure r)
    | Return None -> "\treturn\n"
    | Fn_Call fn_call ->
      (match fn_call.dest with
      | Some dest -> 
        sprintf "\t%s <- %s(%s)\n"
          (Temp.name dest.temp)
          (Symbol.name fn_call.name)
          (Print_utils.pp_list ~f:pp_exp_pure fn_call.arg_list)
      | None -> 
        sprintf "\tvoid %s(%s)\n"
        (Symbol.name fn_call.name)
        (Print_utils.pp_list ~f:pp_exp_pure fn_call.arg_list))
    | Fn_Label fn_label ->
      sprintf ".%s(%s):\n"
        (Symbol.name fn_label.name)
        (Print_utils.pp_list ~f:Assem.format_sized_temp fn_label.param_temps)
    | Alloc a -> 
      sprintf "\t%s <-- alloc(%d)\n"
        (Assem.format_sized_temp a.dest)
        a.typ_size
    | Alloc_arr a -> 
      sprintf "\t%s <-- alloc_array(typ_size:%d,%s)\n"
        (Assem.format_sized_temp a.dest)
      a.typ_size
      (pp_exp_pure a.count)
    | Field_acc_addr f -> 
      sprintf "\t%s <-- %s.(%d)\n"
        (Assem.format_sized_temp f.dest)
        (pp_exp_pure f.struct_)
        f.offset
    | Arr_acc_addr a -> 
      sprintf "\t%s <-- &(%s[%s]) (type size: %d)\n"
        (Assem.format_sized_temp a.dest)
        (pp_exp_pure a.arr)
        (pp_exp_pure a.index)
        a.typ_size
    | Unchecked_read m -> 
      sprintf "\t%s <-- *(%s) (unchecked)\n"
        (Assem.format_sized_temp m.dest)
        (pp_exp_pure m.src)
    | Checked_read m -> 
      sprintf "\t%s <-- *(%s) (checked)\n"
        (Assem.format_sized_temp m.dest)
        (pp_exp_pure m.src)
    | Unchecked_write m -> 
      sprintf "\t*(%s) <-- %s (unchecked)\n"
        (Assem.format_sized_temp m.dest)
        (pp_exp_pure m.src)
    | Checked_write m -> 
      sprintf "\t*(%s) <-- %s (checked)\n"
        (Assem.format_sized_temp m.dest)
        (pp_exp_pure m.src)

  let pp_program prgm = Print_utils.pp_list prgm ~f:pp_command ~sep:""
end
(* ----------------------------------   END PRINT FUNCTIONS   ----------------------------------- *)
 