(* Contains AST Interface implementation, providing functions that elaborate the Parsed Syntax Tree
 * (PST) to the elaborated Abstract Syntax Tree (AST). 
 *  
 * The primary goal of the AST is to modify the parsed tree in a way that simplifies future 
 * operations, while preserving all information necessary for typechecking
 *)

 open Core



 (* ------------------------------------ AST TYPE DEFINITIONS ------------------------------------ *)
 
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
 
 type type_ident = { type_ : type_ ; ident : Symbol.t }
 
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
 
 (* ---------------------------------- END AST TYPE DEFINITIONS ---------------------------------- *)
 (* ---------------------------------   BEGIN PRINT FUNCTIONS   ---------------------------------- *)
 
 module Print =
 struct
   let rec pp_type = function
   | Int -> "int"
   | Bool -> "bool"
   | Type_ident sym -> Symbol.name sym
   | Any_type -> "ANY"
   | Ptr p -> sprintf "%s*" (pp_type p)
   | Arr a -> sprintf "%s[]" (pp_type a)
   | Struct s -> sprintf "struct %s" (Symbol.name s)
 
   let pp_ret_type = function 
   | Some t -> pp_type t
   | None -> "void"

   let pp_asop = function 
   | AEquals -> "="
   | APlus -> "+="
   | AMinus -> "-="
   | ATimes -> "*="
   | ADivided_by -> "/="
   | AModulo -> "%="
   | ABWAnd -> "&="
   | ABWXor -> "^="
   | ABWOr -> "|="
   | ALShift -> "<<="
   | ARShift -> ">>="
 
   let pp_binop_pure = function
   | Plus -> "+"
   | Minus -> "-"
   | Times -> "*"
   | BitwiseAnd -> "&"
   | BitwiseXor -> "^"
   | BitwiseOr -> "|"
 
   let pp_binop_impure = function
   | Divided_by -> "/"
   | Modulo -> "%"
   | LShift -> "<<"
   | RShift -> ">>"
 
   let pp_binop_comp = function
   | LessThan -> "<"
   | LessThanEq ->  "<="
   | GreaterThan -> ">"
   | GreaterThanEq -> ">="
   | EqualsTo -> "=="
   | NotEqualsTo -> "!="
 
   let rec pp_exp = function
   | True -> "true"
   | False -> "false"
   | Var v -> Symbol.name v 
   | Const c -> Int32.to_string c 
   | Null -> "null"
   | Pure p -> sprintf "(%s %s %s)" (pp_a_mexp p.lhs) (pp_binop_pure p.op) (pp_a_mexp p.rhs)
   | Impure i -> sprintf "(%s %s %s)" (pp_a_mexp i.lhs) (pp_binop_impure i.op) (pp_a_mexp i.rhs)
   | Fn_Call f ->
     sprintf "%s (%s)" (Symbol.name f.ident) (Print_utils.pp_list ~f:pp_a_mexp f.arg_list)
   | Comp c -> sprintf "(%s %s %s)" (pp_a_mexp c.lhs) (pp_binop_comp c.op) (pp_a_mexp c.rhs)
   | Bang b -> sprintf "!%s" (pp_a_mexp b)
   | Ternary t -> sprintf "(%s ? %s : %s)" (pp_a_mexp t.cond) (pp_a_mexp t.if_true) (pp_a_mexp t.if_false)
   | Field_acc f -> sprintf "%s.%s" (pp_a_mexp f.struct_) (Symbol.name f.field)
   | Alloc a -> sprintf "alloc(%s)" (pp_type a)
   | Alloc_arr a -> sprintf "alloc(%s,%s)" (pp_type a.type_) (pp_a_mexp a.size)
   | Pointer_dref p -> sprintf "*%s" (pp_a_mexp p)
   | Arr_acc a -> sprintf "%s[%s]" (pp_a_mexp a.arr) (pp_a_mexp a.index)
   and pp_mexp m = pp_exp (Mark.data m)
   and pp_a_mexp am = sprintf "{%s : %s}" (pp_mexp am.mexp) (pp_type am.type_)
 
   let rec n_tabs ~init:acc = function
     | 0 -> acc
     | n -> n_tabs ~init:(" " ^ acc) (n - 1)
 
   let rec pp_stm_depth stm depth =
     let tabs = n_tabs ~init:"" depth in
     match stm with 
     | Declare d -> 
       sprintf "%sDeclare %s %s \n%s{\n%s\n%s}"
         tabs (* Delcare *) (pp_type d.type_) (Symbol.name d.sym) (* \n *)
         tabs (* {\n *)
         (pp_mstm_depth d.mstm (depth + 1)) (* \n *)
         tabs (* } *)
     | Assign a ->
       sprintf 
         "%sAssign %s %s %s;"
         tabs (pp_mexp a.lvalue.mexp) (pp_asop a.asop) (pp_mexp a.amexp.mexp)
     | If i -> 
       sprintf
         "%sif (%s)\n%s{\n%s\n%s} else\n%s{\n%s\n%s}" 
         tabs (* if ( *)(pp_mexp i.cond.mexp) (* )\n *)
         tabs (* {\n *)
         (pp_mstm_depth i.if_true (depth + 1)) (* \n *)
         tabs (* } else\n *)
         tabs (pp_mstm_depth i.if_false (depth + 1)) (* \n *)
         tabs (* } *)
     | While w -> 
       sprintf
         "%swhile (%s) \n%s{\n%s\n%s}" 
         tabs (* while ( *) (pp_mexp w.guard.mexp) (* )\n *) 
         tabs (* {\n *)
         (pp_mstm_depth w.mstm (depth + 1)) (* \n *)
         tabs (* } *)
     | Return (Some r) -> sprintf "%sreturn %s;" tabs (pp_mexp r.mexp)
     | Return None -> sprintf "%sreturn;" tabs
     | Block b ->
       sprintf
         "%sblock\n%s{\n%s%s}" 
         tabs (* block\n*)
         tabs (* {\n *)
         (List.fold_right 
         ~f:(fun m acc -> (pp_mstm_depth m (depth + 1)) ^ "\n" ^ acc) 
         b ~init:"")
         tabs (* } *)
     | Expression e -> sprintf "%s%s;" tabs (pp_mexp e.mexp)
     | ABORT -> sprintf "%sABORT;" tabs
   and pp_mstm_depth m d = pp_stm_depth (Mark.data m) d 
   and pp_stm stm = pp_stm_depth stm 0
 
   let pp_param p = (pp_type p.type_) ^ " " ^ (Symbol.name p.ident)
 
   let pp_typedef (t:typedef) = 
     sprintf 
       "typedef %s %s"
       (pp_type t.type_)
       (Symbol.name t.ident)
 
   let pp_fdefn (f:fdefn) =
     sprintf "%s %s(%s) fn_%s" 
       (pp_ret_type f.ret_type) (Symbol.name f.ident) 
       (Print_utils.pp_list ~f:pp_param f.param_list)
       (pp_stm (Block f.block))
 
   let pp_fdecl (f:fdecl) =
     sprintf
       "%s %s(%s) %s" (pp_ret_type f.ret_type) (Symbol.name f.ident)
       (Print_utils.pp_list ~f:pp_param f.param_list)
       (if f.extern then "extern" else "")
   let pp_sdefn (sdefn:sdefn) =
    sprintf "sdefn(name: %s ; params:[%s])"
      (Symbol.name sdefn.ident)
      (Print_utils.pp_list ~f:pp_param sdefn.field_list) 
 
   let pp_gdecl = function
   | Fdecl f -> pp_fdecl f
   | Fdefn f -> pp_fdefn f
   | Typedef t -> pp_typedef t
   | Sdefn s -> pp_sdefn s
 
   let pp_mgdecl mgd = pp_gdecl (Mark.data mgd)
 
   let pp_program p = Print_utils.pp_list ~f:pp_mgdecl ~sep:"\n" p
 
 end
 
 (* ----------------------------------   END PRINT FUNCTIONS   ----------------------------------- *)
 