(* L4 Compiler
 * Parse Trees
 * Author: Alex Vaynberg
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Elan Biswas (elanb)
 *
 * Forward compatible fragment of C0
 * 
 * The purpose of the parse tree is to make it as easy as possible for the parser to match C0 code
 * to a tree representation, along with a few trivial elaborations, such as ++ or +=.
 *)

 open Core

 (* this is a design decision, I think we could either elaborate this goofily here, or 
    preserve it in here, and elaborate in ir *)
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

 (* Binary operators *)
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
 
 (* Unary operators *)
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
 
 (* Notice that the subexpressions of an expression are marked.
  * (That is, the subexpressions are of type exp Mark.t, not just
  * type exp.) This means that source code location (a src_span) is
  * associated with the subexpression. Currently, the typechecker uses
  * this source location to print more helpful error messages.
  *
  * It's the parser and lexer's job to associate src_span locations with each
  * ast. It's instructive, but not necessary, to closely read the source code
  * for c0_parser.mly, c0_lexer.mll, and parse.ml to get a good idea of how
  * src_spans are created.
  *
  * Check out the Mark module for ways of converting a marked expression into
  * the original expression or to the src_span location. You could also just
  * look at how the typechecker gets the src_span from an expression when it
  * prints error messages.
  *
  * It's completely possible to remove Marks entirely from your compiler, but
  * it will be harder to figure out typechecking errors for later labs.
  *)
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
 (* Expression plus src file location *)
 and mexp = exp Mark.t
 
 (* Declaration *)
 type decl =
   (* <type> x; *)
   | New_var of { typ : type_; sym : Symbol.t }
   (* <type> x = e; *)
   | Init of { typ : type_; sym : Symbol.t; exp : mexp }
 
 (* Simp type from handout *)
 type simp = 
   | PARSE_FAIL (* Used for *x++ and *x-- *)
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
 
 (* Function parameter or struct field *)
 type type_ident = { type_ : type_ ; ident  : Symbol.t }
 
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
 
 
 (* ---------------------------------   BEGIN PRINT FUNCTIONS   ---------------------------------- *)
 module Print = struct

  let pp_asop = function
    | AEquals -> "="
    | APlus  -> "+="
    | AMinus -> "-="
    | ATimes -> "*="
    | ADivided_by -> "/="
    | AModulo -> "%="
    | ABWAnd -> "&="
    | ABWXor -> "%="
    | ABWOr -> "|="
    | ALShift -> "<<="
    | ARShift -> ">>="

   let pp_binop = function
     | Plus -> "+"
     | Minus -> "-"
     | Times -> "*"
     | Divided_by -> "/"
     | Modulo -> "%"
     | LessThan -> "<"
     | LessThanEq -> "<="
     | GreaterThan -> ">"
     | GreaterThanEq -> ">="
     | EqualsTo -> "=="
     | NotEqualsTo -> "!="
     | And -> "&&"
     | Or -> "||"
     | BitwiseAnd -> "&"
     | BitwiseXor -> "^"
     | BitwiseOr -> "|"
     | LShift -> "<<"
     | RShift -> ">>"
   ;;
 
   let pp_unop = function
     | Negative -> "-"
     | Bang -> "!"
     | BitwiseNot -> "~"
   ;;
 
   let rec pp_type_ = function
     | Int -> "int"
     | Bool -> "bool"
     | Type_ident sym -> Symbol.name sym
     | Ptr p -> sprintf "%s*" (pp_type_ p)
     | Arr a -> sprintf "%s[]" (pp_type_ a)
     | Struct s -> sprintf "struct %s" (Symbol.name s)
 
   let pp_ret_type = function
     | Type t -> pp_type_ t
     | Void -> "void"
 
   let rec pp_exp = function
     | Const c -> Int32.to_string c
     | True -> "True"
     | False -> "False"
     | Var id -> Symbol.name id
     | Null -> "NULL"
     | Unop unop -> sprintf "unop(%s(%s))" (pp_unop unop.op) (pp_mexp unop.operand)
     | Binop binop ->
       sprintf "binop(%s %s %s)" (pp_mexp binop.lhs) (pp_binop binop.op) (pp_mexp binop.rhs)
     | Ternary ternary -> 
       sprintf "%s ? %s : %s" 
         (pp_mexp ternary.cond) (pp_mexp ternary.if_true) (pp_mexp ternary.if_false)
     | Fn_Call f ->
       sprintf "fn_call(name: %s ; args: [%s])" 
         (Symbol.name f.ident) (Print_utils.pp_list ~f:pp_mexp f.arg_list)
     | Field_acc f -> sprintf "%s.%s" (pp_mexp f.struct_) (Symbol.name f.field)
     | Field_dref f -> sprintf "%s->%s" (pp_mexp f.struct_) (Symbol.name f.field)
     | Alloc a -> sprintf "alloc(%s)" (pp_type_ a)
     | Pointer_dref p -> sprintf "*%s" (pp_mexp p)
     | Alloc_array a -> sprintf "alloc(%s,%s)" (pp_type_ a.type_) (pp_mexp a.size)
     | Arr_acc a -> sprintf "%s[%s]" (pp_mexp a.arr) (pp_mexp a.index)
 
   and pp_mexp e = pp_exp (Mark.data e)
 
   let pp_decl = function
     | New_var newv -> sprintf "declare(%s, %s)" (pp_type_ newv.typ) (Symbol.name newv.sym)
     | Init initv -> sprintf "declare(%s %s = %s)" 
       (pp_type_ initv.typ) (Symbol.name initv.sym) (pp_mexp initv.exp)
   ;;
 
   let pp_simp = function
     | PARSE_FAIL -> "PARSING FAILED"
     | Declare d -> pp_decl d
     | Assign a -> sprintf "simp(%s %s %s)" (pp_mexp a.lval) (pp_asop a.asop) (pp_mexp a.mexp)
     | Exp e -> sprintf "%s" (pp_mexp e)
   ;;
 
   let rec n_tabs ~init:acc = function
     | 0 -> acc
     | n -> n_tabs ~init:(" " ^ acc) (n - 1)
 
   let rec pp_stm_depth depth stm = 
     let tabs = n_tabs ~init:"" depth in
     match stm with
     | Simp s ->  tabs ^ (pp_simp s)
     | Control c -> pp_ctrl_depth depth c
     | Block b -> 
       sprintf "%s\n%s{\n%s%s}"
         tabs (* block\n *)
         tabs (* {\n *)
         (pp_stms_depth (depth + 1) b) (* Don't need \n bc one added by pp_stms *)
         tabs (* } *)
   and pp_ctrl_depth depth ctrl = 
     let tabs = n_tabs ~init:"" depth in
     match ctrl with
     | If ifctrl -> 
       sprintf 
         "%sif (%s)\n%s{\n%s\n%s}%s" 
         tabs (* if ( *) (pp_mexp ifctrl.cond) (* )\n *)
         tabs (* {\n *)
         (pp_mstm_depth (depth + 1) ifctrl.body) (* \n *)
         tabs (* } *)
         (match ifctrl.els with
         | Some s2 -> 
             (sprintf 
               " else\n%s{\n%s\n%s}" tabs (* {\n *)
               (pp_mstm_depth (depth + 1) s2)) (* \n *)
               tabs (* } *)
         | None -> "")
     | While whlctrl -> 
       sprintf "%swhile (%s)\n%s{\n%s\n%s}"
         tabs (* while ( *) (pp_mexp whlctrl.guard) (* )\n *)
         tabs (* {\n *)
         (pp_mstm_depth (depth + 1) whlctrl.body) (* \n *)
         tabs (* } *)
     | For forctrl -> 
       sprintf "%sfor (%s ; %s ; %s)\n%s{\n%s\n%s}" 
         tabs (* for ( *) 
         (match forctrl.simp1 with | Some stm -> Mark.data stm |> pp_stm | None -> "") (* ; *)
         (pp_mexp forctrl.guard) (* ; *)
         (match forctrl.simp2 with | Some stm -> Mark.data stm |> pp_stm | None -> "")  (* )\n *)
         tabs (* {\n *)
         (pp_mstm_depth (depth + 1) forctrl.body) (* \n *)
         tabs (* } *)
     | Assert e -> sprintf "%sassert (%s)" tabs (pp_mexp e)
     | Return eo -> match eo with 
       | Some e -> sprintf "%sreturn %s;" tabs (pp_mexp e)
       | None -> sprintf "%sreturn;"tabs
   and pp_mstm_depth depth stm = pp_stm_depth depth (Mark.data stm)
   and pp_stms_depth depth stms = String.concat (List.map ~f:(fun stm -> (pp_mstm_depth depth stm)
                                                                         ^ "\n") stms)
   and pp_stm stm = pp_stm_depth 0 stm
 
   let pp_param param = (pp_type_ param.type_) ^ " " ^ (Symbol.name param.ident)
 
   let pp_gdecl = function
     | Fdecl fdecl ->
       sprintf "fdecl(type: %s ; name: %s ; params: [%s] ; extern: %s);"
         (pp_ret_type fdecl.ret_type)
         (Symbol.name fdecl.ident)
         (Print_utils.pp_list ~f:pp_param fdecl.param_list)
         (Bool.to_string fdecl.extern)
     | Fdefn fdefn ->
       sprintf "fdefn(type: %s ; name: %s ; params: [%s])%s"
         (pp_ret_type fdefn.ret_type)
         (Symbol.name fdefn.ident)
         Print_utils.(pp_list ~f:pp_param fdefn.param_list)
         (Block fdefn.block |> pp_stm)
     | Typedef typedef ->
       sprintf "typedef (type: %s ; name: %s)"
         (pp_type_ typedef.type_)
         (Symbol.name typedef.ident)
     | Sdecl sdecl -> 
       sprintf "sdecl(name: %s)" (Symbol.name sdecl)
     | Sdefn sdefn -> 
       sprintf "sdefn(name: %s ; params:[%s])"
         (Symbol.name sdefn.ident)
         (Print_utils.pp_list ~f:pp_param sdefn.field_list)
       
 
   let pp_mdgdecl mgdecl = Mark.data mgdecl |> pp_gdecl
   let pp_program prog = Print_utils.pp_list ~f:pp_mdgdecl ~sep:"\n" prog
 end
 (* ----------------------------------   END PRINT FUNCTIONS   ----------------------------------- *)