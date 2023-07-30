(* L4 Compiler
 * Parse Trees
 * Author: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * 
 * Modified: Elan Biswas (elanb)
 *
 * Forward compatible fragment of C0
 *)
 open Core

  (* Assignment operators *)
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

 (* Binary operator *)
 type binop =
   | Plus
   | Minus
   | Times
   | Divided_by
   | Modulo
   | LessThan
   | LessThanEq
   | GreaterThan
   | GreaterThanEq
   | EqualsTo
   | NotEqualsTo
   | And
   | Or
   | BitwiseAnd
   | BitwiseXor
   | BitwiseOr 
   | LShift
   | RShift
 
 (* Unary operator *)
 type unop = 
   | Negative
   | Bang
   | BitwiseNot
 
 (* Types *)
 type type_ = 
   | Int
   | Bool
   | Type_ident of Symbol.t
   | Ptr of type_
   | Arr of type_
   | Struct of Symbol.t
   [@@deriving equal]
 
 (* Expression *)
 type exp =
   | Const of Int32.t
   | True
   | False
   | Var of Symbol.t
   | Null
   | Unop of {op : unop; operand : mexp }
   | Binop of {op : binop; lhs : mexp; rhs : mexp }
   | Ternary of { cond : mexp; if_true : mexp; if_false : mexp }
   | Fn_Call of { ident : Symbol.t ; arg_list : mexp list }
   | Field_acc of { struct_ : mexp ; field : Symbol.t }
   | Field_dref of { struct_ : mexp ; field : Symbol.t }
   | Alloc of type_
   | Pointer_dref of mexp
   | Alloc_array of { type_ : type_ ; size : mexp }
   | Arr_acc of { arr : mexp ; index : mexp }
 (* Marked expression*)
 and mexp = exp Mark.t
 
 (* Declaration *)
 type decl =
   (* <type> x; *)
   | New_var of {typ : type_; sym : Symbol.t}
   (* <type> x = e; *)
   | Init of {typ : type_; sym : Symbol.t; exp : mexp}
 
 (* Simp type from handout *)
 type simp = 
   | PARSE_FAIL (* Used to avoid opaque and hard-to-test parser errors, specifically in *x++ case *)
   | Declare of decl
   | Assign of { lval : mexp ; asop : asop ; mexp : mexp }
   | Exp of mexp
 
 (* Statement *)
 type stm =
   | Simp of simp
   | Control of control
   | Block of mstm list
 (* Statement plus src file location *)
 and mstm = stm Mark.t
 (* Control *)
 and control = 
   | If of {cond : mexp; body : mstm; els : mstm option}
   | While of {guard : mexp; body : mstm}
   | For of {simp1 : mstm option; guard : mexp; simp2 : mstm option; body : mstm}
   | Assert of mexp
   | Return of mexp option
 
 (* Typedef *)
 type typedef = { type_ : type_ ; ident : Symbol.t }
 
 (* Return type *)
 type ret_type = Type of type_ | Void [@@deriving equal]
 
 (* Function parameter *)
 type type_ident = { type_ : type_ ; ident : Symbol.t }
 
 (* Function definition *)
 type fdefn = 
   { ret_type : ret_type
   ; ident : Symbol.t
   ; param_list : type_ident list
   ; block : mstm list }
 
 (* Function declaration *)
 type fdecl =
  { ret_type : ret_type ; ident : Symbol.t ; param_list : type_ident list ; extern : bool }
  
 (* Struct definition *)
 type sdefn = { ident : Symbol.t ; field_list : type_ident list } 
 
 (* Struct declaration *)
 type sdecl = Symbol.t

 (* Gdecl - top-level function or typedef *)
 type gdecl = Fdecl of fdecl | Fdefn of fdefn | Typedef of typedef | Sdefn of sdefn | Sdecl of sdecl
 (* Marked gdecl *)
 type mgdecl = gdecl Mark.t
 
 (* Program - type of the overall program *)
 type program = mgdecl list
 
 
 (* Print as source, with redundant parentheses *)
 module Print : sig
   val pp_exp : exp -> string
   val pp_stm : stm -> string
   val pp_program : program -> string
 end
 