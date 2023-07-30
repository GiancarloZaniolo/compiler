(* Elaborated AST Signature
 * Author: Elan Biswas (elanb)  
 *)

 type type_ = 
   | Int
   | Bool
   | Type_ident of Symbol.t
   | Any_type
   | Ptr of type_
   | Arr of type_
   | Struct of Symbol.t
   [@@deriving equal]

type ret_type = type_ option

type asop = 
  | AEquals
  | APlus
  | AMinus
  | ATimes
  | ADivided_by
  | AModulo
  | ABWAnd
  | ABWXor
  | ABWOr
  | ALShift
  | ARShift

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

type exp = 
  | Const of Int32.t
  | True
  | False
  | Var of Symbol.t
  | Null
  | Pure of { lhs: annotated_mexp ; op : binop_pure ; rhs : annotated_mexp }
  | Impure of { lhs: annotated_mexp ; op : binop_impure ; rhs : annotated_mexp }
  | Fn_Call of { ident : Symbol.t ; arg_list : annotated_mexp list }
  | Comp of { lhs: annotated_mexp ; op : binop_comp ; rhs : annotated_mexp }
  | Bang of annotated_mexp
  | Ternary of { cond : annotated_mexp ; if_true : annotated_mexp ; if_false : annotated_mexp }
  | Field_acc of { struct_ : annotated_mexp ; field : Symbol.t }
  | Alloc of type_
  | Alloc_arr of { type_ : type_ ; size : annotated_mexp }
  | Pointer_dref of annotated_mexp
  | Arr_acc of { arr : annotated_mexp ; index : annotated_mexp }
and mexp = exp Mark.t
and annotated_mexp = { mexp : mexp ; type_ : type_ }

type stm =
  | Declare of { type_ : type_ ; sym : Symbol.t ; mstm : mstm }
  | Assign of { lvalue : annotated_mexp ; asop : asop ; amexp : annotated_mexp } 
  | If of { cond : annotated_mexp ; if_true : mstm ; if_false : mstm }
  | While of { guard : annotated_mexp ; mstm : mstm }
  | Return of annotated_mexp option
  | Block of mstm list
  | Expression of annotated_mexp
  | ABORT
and mstm = stm Mark.t

type typedef = { type_ : type_ ; ident : Symbol.t }

type type_ident = { type_ : type_ ; ident  : Symbol.t }

type fdefn = 
 { ret_type : ret_type
 ; ident : Symbol.t
 ; param_list : type_ident list
 ; block : mstm list }

type fdecl = 
 { ret_type : ret_type ; ident : Symbol.t ; param_list : type_ident list ; extern : bool }

type sdefn = { ident : Symbol.t ; field_list : type_ident list } 


type gdecl = Fdecl of fdecl | Fdefn of fdefn | Typedef of typedef | Sdefn of sdefn
type mgdecl = gdecl Mark.t

type program = mgdecl list

module Print : sig
 val pp_type : type_ -> string
 val pp_ret_type : type_ option -> string
 val pp_binop_pure : binop_pure -> string
 val pp_binop_impure : binop_impure -> string
 val pp_binop_comp : binop_comp -> string
 val pp_exp : exp -> string
 val pp_stm : stm -> string
 val pp_program : program -> string
end