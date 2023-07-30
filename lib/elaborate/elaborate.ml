(* Functionality to elaborate parsed tree to what will be typechecked *)

open Core

module P = Pst
module A = Ast

let dummy_type = Symbol.symbol "" |> A.Type_ident

(* ------------------------------ BEGIN HELPERS FOR ERROR MESSAGES ------------------------------ *)

(* remark marked a ==> A mark with the same span of marked and data a  *)
let remark marked a = Mark.map ~f:(fun _ -> a) marked ;;
let span_from_list ms = List.map ~f:Mark.src_span ms |> Mark.wrap ;;

(* For printing error messages *)
let elab_errors : Error_msg.t = Error_msg.create () ;;
let raise_error ~(msg : string) (ma : 'a Mark.t) = 
  Error_msg.error elab_errors (Mark.src_span ma) ~msg:msg; 
  raise Error_msg.Error 
;;

(* ------------------------------- END HELPERS FOR ERROR MESSAGES ------------------------------- *)
(* --------------------------------   BEGIN TYPE ELABORATIONS   --------------------------------- *)

let rec elaborate_type : P.type_ -> A.type_ = function
  | P.Int -> A.Int
  | P.Bool -> A.Bool
  | P.Type_ident i -> A.Type_ident i
  | P.Ptr type_ -> elaborate_type type_ |> A.Ptr
  | P.Arr type_ -> elaborate_type type_ |> A.Arr
  | P.Struct s -> A.Struct s
;;

let elaborate_typedef (td : P.typedef) : A.typedef = 
  { type_ = elaborate_type td.type_ ; ident = td.ident }
;;

let elaborate_ret_type : P.ret_type -> A.ret_type = function 
| P.Type t -> Some (elaborate_type t) 
| P.Void -> None
;;

(* ---------------------------------   END TYPE ELABORATIONS   ----------------------------------- *)
(* -----------------------------   BEGIN EXPRESSION ELABORATIONS   ------------------------------ *)

let elaborate_binop_pure : P.binop -> A.binop_pure = function
  | P.Plus -> A.Plus
  | P.Minus -> A.Minus
  | P.Times -> A.Times
  | P.BitwiseAnd -> A.BitwiseAnd
  | P.BitwiseXor -> A.BitwiseXor
  | P.BitwiseOr -> A.BitwiseOr
  | _ -> failwith "Expected a pure binary operator"
;;

let elaborate_binop_impure : P.binop -> A.binop_impure = function
  | P.Divided_by -> A.Divided_by
  | P.Modulo -> A.Modulo
  | P.LShift -> A.LShift
  | P.RShift -> A.RShift
  | _ -> failwith "Expected an impure binary operator"
;;

let elaborate_binop_comp : P.binop -> A.binop_comp = function
  | P.LessThan -> A.LessThan
  | P.LessThanEq -> A.LessThanEq
  | P.GreaterThan -> A.GreaterThan
  | P.GreaterThanEq -> A.GreaterThanEq
  | P.EqualsTo -> A.EqualsTo
  | P.NotEqualsTo -> A.NotEqualsTo
  | _ -> failwith "Expected an comparison binary operator"
;;

let rec elaborate_mexp (mexp : P.mexp) : A.mexp =
  (* Helper functions *)
  let elaborate_binop_exp (binop_exp : P.exp) : A.exp =
    match binop_exp with
    | P.Binop exp -> 
      let lhs' : A.annotated_mexp = { mexp = elaborate_mexp exp.lhs ; type_ = dummy_type } in
      let rhs': A.annotated_mexp = { mexp = elaborate_mexp exp.rhs ; type_ = dummy_type } in
      let annotated_false : A.annotated_mexp = { mexp = Mark.naked A.False ; type_ = A.Bool } in
      let annotated_true : A.annotated_mexp = { mexp = Mark.naked A.True ; type_ = A.Bool } in
      (match exp.op with
      | P.Plus | P.Minus | P.Times | P.BitwiseAnd | P.BitwiseXor | P.BitwiseOr -> 
        Pure { lhs = lhs' ; op = elaborate_binop_pure exp.op ; rhs = rhs' } 
      | P.Divided_by | P.Modulo | P.LShift | P.RShift ->
        Impure { lhs = lhs' ; op = elaborate_binop_impure exp.op ; rhs = rhs'}
      | P.LessThan | P.LessThanEq | P.GreaterThan | P.GreaterThanEq | P.EqualsTo | P.NotEqualsTo ->
        Comp { lhs = lhs' ; op = elaborate_binop_comp exp.op ; rhs = rhs' }
      | P.And -> A.Ternary { cond = lhs' ; if_true = rhs' ; if_false = annotated_false }
      | P.Or -> A.Ternary { cond = lhs' ; if_true = annotated_true ; if_false = rhs' }
      )
    | _ -> failwith "Expected a binary operator expression"
  in
  let elaborate_unop_exp (unop_exp : P.exp) : A.exp =
    match unop_exp with
    | P.Unop exp -> (match exp.op with
      | P.Negative ->
        Pure { lhs = { mexp = Int32.of_int_exn 0 |> A.Const |> Mark.naked ; type_ = A.Int }
              ; op = A.Minus
              ; rhs ={ mexp = elaborate_mexp exp.operand ; type_ = A.Int } }
      | P.Bang -> A.Bang { mexp = elaborate_mexp exp.operand ; type_ = A.Bool }
      | P.BitwiseNot ->
        Pure { lhs = { mexp = elaborate_mexp exp.operand ; type_ = A.Int }
             ; op = A.BitwiseXor
             ; rhs = { mexp = Int32.of_int_exn (-1) |> A.Const |> Mark.naked ; type_ = A.Int } })
    | _ -> failwith "Expected a unary operator expression"
  in
  (* Expression elaboration *)
  let exp = Mark.data mexp in
  let exp' = match exp with
  | P.True -> A.True
  | P.False -> A.False
  | P.Var s -> A.Var s  
  | P.Const i -> A.Const i
  | P.Null -> A.Null
  | P.Binop _ -> elaborate_binop_exp exp
  | P.Unop _ -> elaborate_unop_exp exp
  | P.Ternary tern ->
    A.Ternary { cond = { mexp = elaborate_mexp tern.cond ; type_ = A.Bool }
            ; if_true = { mexp = elaborate_mexp tern.if_true ; type_ = dummy_type }
            ; if_false = { mexp = elaborate_mexp tern.if_false ; type_ = dummy_type } } 
  | P.Fn_Call f ->
    let elab_and_annotate (arg : P.mexp) : A.annotated_mexp =
      let mexp = elaborate_mexp arg in
      let type_ = dummy_type in
      { mexp ; type_ }
    in
    A.Fn_Call { ident = f.ident; arg_list = List.map f.arg_list ~f:elab_and_annotate }
  | Field_acc fa ->
    A.Field_acc { struct_ = { mexp = elaborate_mexp fa.struct_ ; type_ = dummy_type }
                ; field = fa.field}
  | P.Field_dref fd ->
    let struct_dref = 
      A.Pointer_dref { mexp = elaborate_mexp fd.struct_ ; type_ = dummy_type } 
      |> remark fd.struct_
    in
    let annotated_struct_dref : A.annotated_mexp = { mexp = struct_dref ; type_ = dummy_type } in
    A.Field_acc { struct_ = annotated_struct_dref ; field = fd.field }
  | P.Alloc type_ -> elaborate_type type_ |> A.Alloc
  | P.Pointer_dref mexp -> A.Pointer_dref { mexp = elaborate_mexp mexp ; type_ = dummy_type }
  | P.Alloc_array aa ->
    let size : A.annotated_mexp = { mexp = elaborate_mexp aa.size ; type_ = dummy_type } in
    A.Alloc_arr { type_ = elaborate_type aa.type_ ; size = size }
  | P.Arr_acc aa ->
    let arr : A.annotated_mexp = { mexp = elaborate_mexp aa.arr ; type_ = dummy_type } in
    let index : A.annotated_mexp = { mexp = elaborate_mexp aa.index ; type_ = A.Int } in
    A.Arr_acc { arr ; index }

  in
  remark mexp exp' 
;;

(* ------------------------------   END EXPRESSION ELABORATIONS   ------------------------------ *)
(* -----------------------------    BEGIN STATEMENT ELABORATIONS   ----------------------------- *)

(* Helper functions *)
let make_mwhile mguard mbody = 
  let stm = A.While { guard = mguard ; mstm = mbody } in
  Mark.mark' stm (Mark.wrap [ Mark.src_span mguard.mexp ; Mark.src_span mbody ])
;;

let mstms_to_block mstms = span_from_list mstms |> Mark.mark' (A.Block mstms) ;;
let p_mstms_to_block mstms = span_from_list mstms |> Mark.mark' (P.Block mstms) ;;

let combine_mstms mstm1 mstm2 = mstms_to_block [mstm1 ; mstm2] ;;

let elaborate_asop = function 
  | P.AEquals -> A.AEquals
  | P.APlus -> A.APlus
  | P.AMinus -> A.AMinus
  | P.ATimes -> A.ATimes
  | P.ADivided_by -> A.ADivided_by
  | P.AModulo -> A.AModulo
  | P.ABWAnd -> A.ABWAnd
  | P.ABWXor -> A.ABWXor
  | P.ABWOr -> A.ABWOr
  | P.ALShift -> A.ALShift
  | P.ARShift -> A.ARShift

(* All statement elaboration *)
let rec elaborate_mstm (mstm : P.mstm) : A.mstm =
  let error ~msg = raise_error ~msg mstm in
  (* Helper functions *)
  let elaborate_simp : P.simp -> A.stm = function
    | PARSE_FAIL -> error ~msg:"Couldn't parse statement"
    | P.Declare decl -> elaborate_decl decl (mstms_to_block [])
    | P.Assign asn ->
      let lvalue : A.annotated_mexp = { mexp = elaborate_mexp asn.lval ; type_ = dummy_type } in
      let asop : A.asop = elaborate_asop asn.asop in
      let amexp : A.annotated_mexp = { mexp = elaborate_mexp asn.mexp ; type_ = dummy_type } in
      A.Assign { lvalue ; asop ; amexp }
    | P.Exp mexp -> A.Expression { mexp = elaborate_mexp mexp ; type_ = dummy_type }
  in
  let elseopt_to_mstmt : P.mstm option -> A.mstm = function
    | None -> Mark.mark' (A.Block []) None
    | Some p_mstm -> elaborate_mstm p_mstm
  in
  let elaborate_ctrl : P.control -> A.stm = function
    | P.If if_stm ->
      A.If { cond = { mexp = elaborate_mexp if_stm.cond ; type_ = dummy_type }
           ; if_true = elaborate_mstm if_stm.body
           ; if_false = elseopt_to_mstmt if_stm.els }
    | P.While while_stm -> 
      A.While { guard = { mexp = elaborate_mexp while_stm.guard ; type_ = A.Bool }
              ; mstm = elaborate_mstm while_stm.body }
    | P.For for_stm -> elaborate_for (P.For for_stm)
    | P.Assert asn_stm ->
      A.If { cond = { mexp = elaborate_mexp asn_stm ; type_ = A.Bool }
           ; if_true = remark asn_stm (A.Block []) 
           ; if_false = remark asn_stm A.ABORT }
    | P.Return (Some mexp) -> A.Return (Some { mexp = elaborate_mexp mexp ; type_ = dummy_type })
    | P.Return None -> A.Return None
  in

  (* Statement elaboration *)
  let stm' =
    match Mark.data mstm with
    | P.Block mstms -> elaborate_block mstms
    | P.Simp simp -> elaborate_simp simp
    | P.Control ctrl -> elaborate_ctrl ctrl 
  in remark mstm stm'

and elaborate_block : (P.mstm list) -> A.stm = function
  | [] -> A.Block []
  | p_mstm :: p_mstmss -> 
    let (mstm, stmss) = (elaborate_mstm p_mstm, elaborate_block p_mstmss) in
    let mstmss = span_from_list p_mstmss |> Mark.mark' stmss in
    match Mark.data p_mstm with
    (* We case on the parsed first statement rather than the elaborated first statement to avoid
        losing scoping information on declarations within blocks. i.e if we have a block of the
        form "block { block { declare(v,t,e), stm1, stm2 }, stm3, stm4 }," we want to avoid having
        stm3 and stm4 within the scope of the declare. *)
    | P.Simp (P.Declare decl) -> elaborate_decl decl mstmss
    | _ ->
      match stmss with
      | A.Block stmss' -> A.Block (mstm::stmss') 
      | _ -> A.Block [mstm ; mstmss]
and elaborate_decl decl mstm_in_scope =
  match decl with
  | P.New_var d -> 
    A.Declare { type_ = elaborate_type d.typ ; sym = d.sym ; mstm = mstm_in_scope }
  | P.Init i ->
    let amexp : A.annotated_mexp = { mexp = elaborate_mexp i.exp ; type_ = dummy_type } in
    let temp_var_sym = Tempvar.create () |> Tempvar.name |> Symbol.symbol in
    let temp_var = temp_var_sym |> A.Var |> Mark.naked in
    let temp_lvalue : A.annotated_mexp = { mexp = temp_var ; type_ = dummy_type } in 
    let asn_mstm_1 =
      A.Assign { lvalue = temp_lvalue ; asop = A.AEquals ; amexp } |> remark amexp.mexp
    in
    let var : A.annotated_mexp = { mexp = A.Var i.sym |> Mark.naked ; type_ = dummy_type } in
    let asn_mstm_2 = 
      A.Assign { lvalue = var ; asop = A.AEquals ; amexp = temp_lvalue } |> Mark.naked
    in
    let type_ = elaborate_type i.typ in
    let real_mdecl = 
      A.Declare
        { type_
        ; sym = i.sym
        ; mstm = A.Block [ asn_mstm_2 ; mstm_in_scope ] |> remark mstm_in_scope } 
      |> remark mstm_in_scope in
    let mstm = mstms_to_block [ asn_mstm_1 ; real_mdecl ] in
    A.Declare { type_ ; sym = temp_var_sym ; mstm }
and elaborate_for : P.control -> A.stm = function
  | P.For for_stm -> 
    let step = match for_stm.simp2 with
    | Some mstm ->
      (match Mark.data mstm with
      | P.Simp (P.Declare _) -> raise_error mstm ~msg:"For loop third component is a declaration"
      | P.Simp _ -> elaborate_mstm mstm
      | _ -> raise_error mstm ~msg:"The third component of a for loop must be a simple statement")
    | None -> A.Block [] |> Mark.naked
    in
    let mbody = combine_mstms (elaborate_mstm for_stm.body) step in
    let mguard : A.annotated_mexp = { mexp = elaborate_mexp for_stm.guard ; type_ = A.Bool } in
    let mwhile = make_mwhile mguard mbody in
    (match for_stm.simp1 with
    | Some mstm ->
      (match Mark.data mstm with
      | P.Simp (P.Declare decl) -> elaborate_decl decl mwhile
      | P.Simp _ -> A.Block [ elaborate_mstm mstm ; mwhile ]
      | _ -> raise_error mstm ~msg:("First component of for loop is not a simple statement"))
    | None -> A.Block [ mwhile ])
  | _ -> failwith "Expected a for statement"
;;

(* -----------------------------   END STATEMENT ELABORATIONS   ----------------------------- *)
(* --------------------------------   BEGIN GDECL ELABORATIONS   -------------------------------- *)

let elaborate_type_ident (p : P.type_ident) : A.type_ident =
  { type_ = elaborate_type p.type_ ; ident = p.ident }
;;

(* Preserve extern-ness of a function for typechecking so we don't have to case on function names *)
let elaborate_fdecl (fl : P.fdecl) : A.fdecl = 
  { ret_type = elaborate_ret_type fl.ret_type 
  ; ident = fl.ident 
  ; param_list = List.map fl.param_list ~f:elaborate_type_ident 
  ; extern = fl.extern }
;;

let elaborate_fdefn (fn : P.fdefn) : A.fdefn = 
  let fn_block = [ elaborate_mstm (p_mstms_to_block fn.block) ] in
  let block' = 
    if P.equal_ret_type fn.ret_type P.Void then List.append fn_block [Mark.naked (A.Return None)] 
    else fn_block
  in
  { ret_type = elaborate_ret_type fn.ret_type 
  ; ident = fn.ident 
  ; param_list = List.map fn.param_list ~f:elaborate_type_ident
  ; block = block' }
;;

let elaborate_sdefn (sd : P.sdefn) : A.sdefn =
  { ident = sd.ident ; field_list = List.map ~f:elaborate_type_ident sd.field_list }

let elaborate_gdecl : P.gdecl -> A.gdecl option = function
  | P.Fdecl f -> A.Fdecl (elaborate_fdecl f) |> Some
  | P.Fdefn f -> A.Fdefn (elaborate_fdefn f) |> Some
  | P.Typedef td -> A.Typedef (elaborate_typedef td) |> Some
  | P.Sdecl _ -> None
  | P.Sdefn sd -> A.Sdefn (elaborate_sdefn sd) |> Some
;;

let elaborate_mgdecl (g : P.mgdecl) : A.mgdecl option = 
  match (elaborate_gdecl (Mark.data g)) with
  | Some gdecl -> remark g gdecl |> Some
  | None -> None
;;

(* ---------------------------------   END GDECL ELABORATIONS   --------------------------------- *)
(* -----------------------------------   INTERFACE FUNCTION   ----------------------------------- *)

let elaborate (p : P.program) : A.program = 
  let cons_opt o acc =
    match o with
    | Some mg -> mg :: acc
    | None -> acc
  in
  let acc_rev = List.fold p ~init:[] ~f:(fun acc l ->  cons_opt (elaborate_mgdecl l) acc) in
  List.rev acc_rev
;;

(* ------------------------------------- BEGIN EXPECT TESTS ------------------------------------- *)

let%expect_test "Test parsing of an empty program" =
  let lexbuf =
    Lexing.from_string "int main() {int x = 3; int y = -x + 4; return x + y * x / 3; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     Declare int $TEMP4
     {
      block
      {
       Assign $TEMP4 = 3;
       Declare int x
       {
        block
        {
         Assign x = $TEMP4;
         Declare int $TEMP2
         {
          block
          {
           Assign $TEMP2 = ({({0 : int} - {x : int}) : } + {4 : });
           Declare int y
           {
            block
            {
             Assign y = $TEMP2;
             block
             {
              return ({x : } + {({({y : } * {x : }) : } / {3 : }) : });
             }
            }
           }
          }
         }
        }
       }
      }
     }
    }
  |}]
;;

let%expect_test "Text parsing of lvalue wrapped in parens" =
  let lexbuf =
    Lexing.from_string "int main() { int x = 5; (x) = 6; (x); return (x); }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     Declare int $TEMP6
     {
      block
      {
       Assign $TEMP6 = 5;
       Declare int x
       {
        block
        {
         Assign x = $TEMP6;
         block
         {
          Assign x = 6;
          x;
          return x;
         }
        }
       }
      }
     }
    }
  |}]
;;

let%expect_test "Text parsing of unary op combined with binary op in one line" =
  let lexbuf =
    Lexing.from_string "int main() { -x-y; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     block
     {
      ({({0 : int} - {x : int}) : } - {y : });
     }
    }
  |}]
;;

let%expect_test "Text parsing of dangling else" =
  let lexbuf =
    Lexing.from_string "int main() { if (a) if (b) s; else s2; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     block
     {
      if (a)
      {
       if (b)
       {
        s;
       } else
       {
        s2;
       }
      } else
      {
       block
       {
       }
      }
     }
    }
  |}]
;;

let%expect_test "Text parsing of big paren lvalue" =
  let lexbuf =
    Lexing.from_string "int main() { ((((((((x)))))))) = 7; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     block
     {
      Assign x = 7;
     }
    }
  |}]
;;

let%expect_test "Text parsing of expression wrapped in many parens" =
  let lexbuf =
    Lexing.from_string "int main() { ((((((((x - 1)))))))); }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     block
     {
      ({x : } - {1 : });
     }
    }
  |}]
;;

let%expect_test "Text parsing of a normal for loop" =
  let lexbuf =
    Lexing.from_string "int main() { for (int i =0; i < 10; i++) int x; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     block
     {
      Declare int $TEMP7
      {
       block
       {
        Assign $TEMP7 = 0;
        Declare int i
        {
         block
         {
          Assign i = $TEMP7;
          while (({i : } < {10 : }))
          {
           block
           {
            Declare int x
            {
             block
             {
             }
            }
            Assign i += 1;
           }
          }
         }
        }
       }
      }
     }
    }
  |}]
;;

let%expect_test "Test parsing of just a typedef" =
  let lexbuf =
    Lexing.from_string "typedef int hello;"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    typedef int hello
  |}]
;;

let%expect_test "Test parsing of just an fdecl without params" =
  let lexbuf =
    Lexing.from_string "int f();"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int f()
  |}]
;;

let%expect_test "Test parsing of just an fdecl with params" =
  let lexbuf =
    Lexing.from_string "int f(int x, bool y);"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int f(int x, bool y)
  |}]
;;

let%expect_test "Test parsing of just an fdefn without params and empty body" =
  let lexbuf =
    Lexing.from_string "int f(){}"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int f() fn_block
    {
     block
     {
     }
    }
  |}]
;;

let%expect_test "Test parsing of just an fdefn with params and simple body" =
  let lexbuf =
    Lexing.from_string "int f(int x, bool y){ int x; x = 6; return x; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int f(int x, bool y) fn_block
    {
     Declare int x
     {
      block
      {
       Assign x = 6;
       return x;
      }
     }
    }
  |}]
;;

let%expect_test "Test parsing from a header and source file" =
  let source_filename = "/autograder/dist/compiler/tests/expect/busy.l3" in
  let header_filename = Some "/autograder/dist/compiler/tests/expect/busy.h0" in
  let program = Parse.parse ~source_filename ~header_filename in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int busy_beaver(int symbols, int states) extern
    int main() fn_block
    {
     block
     {
      if (({6 : } == {busy_beaver ({2 : }, {2 : }) : }))
      {
       block
       {
       }
      } else
      {
       ABORT;
      }
      if (({21 : } == {busy_beaver ({2 : }, {3 : }) : }))
      {
       block
       {
       }
      } else
      {
       ABORT;
      }
      if (({107 : } == {busy_beaver ({2 : }, {4 : }) : }))
      {
       block
       {
       }
      } else
      {
       ABORT;
      }
      return busy_beaver ({4 : }, {2 : });
     }
    }
  |}]
;;

let%expect_test "Test parsing of a void fdefn with params and simple body" =
  let lexbuf =
    Lexing.from_string "void f(int x, bool y){ int x; x = 6; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    void f(int x, bool y) fn_block
    {
     Declare int x
     {
      block
      {
       Assign x = 6;
      }
     }
     return;
    }
  |}]
;;

let%expect_test "Test parsing of (*x)++" =
  let lexbuf =
    Lexing.from_string "int main(){ (*x)++; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     block
     {
      Assign *{x : } += 1;
     }
    }
  |}]
;;

let%expect_test "Test parsing of arrays" =
  let lexbuf =
    Lexing.from_string "int main(){ int[] x = alloc_array(int, 7+12/3); x[3] = 4; return x[0]; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     Declare int[] $TEMP9
     {
      block
      {
       Assign $TEMP9 = alloc(int,{({7 : } + {({12 : } / {3 : }) : }) : });
       Declare int[] x
       {
        block
        {
         Assign x = $TEMP9;
         block
         {
          Assign {x : }[{3 : int}] = 4;
          return {x : }[{0 : int}];
         }
        }
       }
      }
     }
    }
  |}]
;;

let%expect_test "Test parsing of pointer declaration/multiplication ambiguity " =
  let lexbuf =
    Lexing.from_string "typedef bool hi; int main(){ hi *x; ho * y; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    typedef bool hi
    int main() fn_block
    {
     Declare hi* x
     {
      block
      {
       ({ho : } * {y : });
      }
     }
    }
  |}]
;;

let%expect_test "Test parsing of struct declaration " =
  let lexbuf =
    Lexing.from_string " struct hello; "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {| |}]
;;

let%expect_test "Test parsing of struct definition " =
  let lexbuf =
    Lexing.from_string " struct hello { int x; bool[] y; int* z; }; "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    sdefn(name: hello ; params:[int x, bool[] y, int* z])
  |}]
;;

let%expect_test "Test parsing of struct definition with typedef field " =
  let lexbuf =
    Lexing.from_string " typedef int goodbye ; struct hello { int x; bool[] y; goodbye* z; }; "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    typedef int goodbye
    sdefn(name: hello ; params:[int x, bool[] y, goodbye* z])
  |}]
;;

let%expect_test "Test parsing of struct accesses" =
  let lexbuf =
    Lexing.from_string " struct hello { int x; bool[] y; };
                         int main() { struct hello h; h.x = 7; h.y = alloc_array(bool, 7); } "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    sdefn(name: hello ; params:[int x, bool[] y])
    int main() fn_block
    {
     Declare struct hello h
     {
      block
      {
       Assign {h : }.x = 7;
       Assign {h : }.y = alloc(bool,{7 : });
      }
     }
    }
  |}]
;;

let%expect_test "Test parsing of struct dereferences" =
  let lexbuf =
    Lexing.from_string " struct hello { int x; bool[] y; };
                         int main() { struct hello *h; h->x = 7; h->y = alloc_array(bool, 7); } "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    sdefn(name: hello ; params:[int x, bool[] y])
    int main() fn_block
    {
     Declare struct hello* h
     {
      block
      {
       Assign {*{h : } : }.x = 7;
       Assign {*{h : } : }.y = alloc(bool,{7 : });
      }
     }
    }
  |}]
;;

let%expect_test "Test parsing of pointer deref" =
  let lexbuf =
    Lexing.from_string "int main() { bool *h; *h = true; return *h ? 0 : 1; } "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  let ast = elaborate program in
  print_endline (A.Print.pp_program ast);
  [%expect
    {|
    int main() fn_block
    {
     Declare bool* h
     {
      block
      {
       Assign *{h : } = true;
       return ({*{h : } : bool} ? {0 : } : {1 : });
      }
     }
    }
  |}]
;;
