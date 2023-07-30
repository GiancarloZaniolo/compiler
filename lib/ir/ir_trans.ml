(* L4 Compiler
 * Implementation of AST->IRT translation
 * Author: Giancarlo Zaniolo (gzaniolo)
 *)

open Core

module S = Symbol.Map
module SHT = Symbol.Table
module SH = Symbol.Hash_set

module A = Ast
module L = Assem.Label
module T = Typechecker
module I = Ir_tree
module As = Assem

type struct_info = { flds_info : (int * A.type_) SHT.t ; size : int ; align : As.x86_operand_size }

type env =
  { sym2temp : As.sized_temp S.t
  ; gdecl_ctxts : T.gdecl_ctxts
  ; structs_info : struct_info SHT.t
  }

(*--------------------------------------BEGIN HELPERS---------------------------------------------*)

let translate_name (sym : Symbol.t) (fdecl_ctxt : T.fdecl_status T.SHT.t) =
  let sym_fdecl = T.SHT.find_exn fdecl_ctxt sym in
  if sym_fdecl.fdecl.extern then sym
  else sprintf "_c0_%s" (Symbol.name sym) |> Symbol.symbol

let rec type_opsize (td_ctxt : A.type_ SHT.t) = function
  | A.Int | A.Bool -> As.S_32
  | A.Ptr _ | A.Arr _ | A.Struct _-> As.S_64
  | A.Type_ident t -> type_opsize td_ctxt (SHT.find_exn td_ctxt t)
  | A.Any_type -> failwith "Should never need to know size of 'any' type"

let rec type_size (td_ctxt : A.type_ SHT.t) (structs_info : struct_info SHT.t) = function
  | A.Int | A.Bool -> 4
  | A.Ptr _ | A.Arr _ -> 8
  | A.Type_ident t -> type_size td_ctxt structs_info (SHT.find_exn td_ctxt t)
  | A.Struct s -> (SHT.find_exn structs_info s).size
  | A.Any_type -> failwith "Should never need to know size of 'any' type"

let rec type_size_align (td_ctxt : A.type_ SHT.t) (structs_info : struct_info SHT.t) = function
  | A.Int | A.Bool -> (4, As.S_32)
  | A.Ptr _ | A.Arr _ -> (8, As.S_64)
  | A.Type_ident t -> type_size_align td_ctxt structs_info (SHT.find_exn td_ctxt t)
  | A.Struct s -> 
    let info = (SHT.find_exn structs_info s) in 
    (info.size, info.align)
  | A.Any_type -> failwith "Should never need to know size of 'any' type"



(*----------------------------------------END HELPERS---------------------------------------------*)


let binop_pure_ir = function
  | A.Plus -> I.Plus
  | A.Minus -> I.Minus
  | A.Times -> I.Times
  | A.BitwiseAnd -> I.BitwiseAnd
  | A.BitwiseXor -> I.BitwiseXor
  | A.BitwiseOr -> I.BitwiseOr

let binop_impure_ir = function
  | A.Divided_by -> I.Divided_by
  | A.Modulo -> I.Modulo
  | A.LShift -> I.LShift
  | A.RShift -> I.RShift

let binop_comp_ir = function
  | A.LessThan -> I.LessThan
  | A.LessThanEq -> I.LessThanEq
  | A.GreaterThan -> I.GreaterThan
  | A.GreaterThanEq -> I.GreaterThanEq
  | A.EqualsTo -> I.EqualsTo
  | A.NotEqualsTo -> I.NotEqualsTo

let rec amexp_ir
  (amexp : A.annotated_mexp) (acc : I.command list) (env : env) : I.command list * I.exp_pure = 
  match Mark.data amexp.mexp with
  | A.True -> (acc, I.Const32 Int32.one)
  | A.False -> (acc, I.Const32 Int32.zero)
  | A.Var v -> (acc, I.Temp (S.find_exn env.sym2temp v))
  | A.Const c -> (acc, I.Const32 c) 
  | A.Pure p -> 
    let (acc1, e1) = amexp_ir p.lhs acc env in 
    let (acc2, e2) = amexp_ir p.rhs acc1 env in
    (acc2, I.Binop_pure {lhs = e1; op = binop_pure_ir p.op; rhs = e2})
  | A.Impure i -> 
    let (acc1, e1) = amexp_ir i.lhs acc env in 
    let (acc2, e2) = amexp_ir i.rhs acc1 env in 
    (* Invariant: Impure ops will always have int operands *)
    let t : As.sized_temp = { temp = Temp.create () ; size = As.S_32 } in 
    ((I.Binop_impure {lhs = e1; op = binop_impure_ir i.op; rhs = e2; dest = t}) :: acc2, I.Temp t)
  | A.Comp _ -> 
    let l1 = Local_label.create () in
    let l2 = Local_label.create () in
    let l3 = Local_label.create () in 
    let temp : As.sized_temp =
       { temp = Temp.create () ; size = (type_opsize env.gdecl_ctxts.typedef_ctxt amexp.type_) } in
    let acc1 = bool_jmp_ir amexp.mexp l1 l2 acc env in
    let acc2 = 
      (I.Goto l3) :: (I.Move {src = I.Const32 Int32.one; dest = temp}) :: (I.Label l1) :: acc1
    in
    let acc3 = 
      (I.Goto l3) :: (I.Move {src = I.Const32 Int32.zero; dest = temp}) :: (I.Label l2) :: acc2
    in 
    ((I.Label l3) :: acc3, I.Temp temp)  
    | A.Bang b -> 
    let l1 = Local_label.create () in
    let l2 = Local_label.create () in
    let l3 = Local_label.create () in
    (* Invariant: Bang should always have operand of type bool *)
    let temp : As.sized_temp = { temp = Temp.create() ; size = As.S_32 } in 
    let acc1 = abool_jmp_ir b l2 l1 acc env in
    let acc2 = 
      (I.Goto l3) :: (I.Move {src = I.Const32 Int32.one; dest = temp}) :: (I.Label l1) :: acc1
    in 
    let acc3 = 
      (I.Goto l3) :: (I.Move {src = I.Const32 Int32.zero; dest = temp}) :: (I.Label l2) :: acc2
    in 
    ((I.Label l3) :: acc3, I.Temp temp)
  | A.Ternary t -> 
    let l1 = Local_label.create () in
    let l2 = Local_label.create () in
    let l3 = Local_label.create () in
    let temp : As.sized_temp = 
      { temp = Temp.create () ; size = (type_opsize env.gdecl_ctxts.typedef_ctxt amexp.type_) } in
    let acc1 = abool_jmp_ir t.cond l1 l2 acc env in
    let acc2 = (I.Label l1) :: acc1 in (*if it is l1 then do all calculations*)
    let (acc3, e1) = amexp_ir t.if_true acc2 env in 
    let acc4 = (I.Goto l3) :: (I.Move {src = e1; dest = temp}) :: acc3 in
    let acc5 = (I.Label l2) :: acc4 in (*if it is l2 then do all calculations*)
    let (acc6, e2) = amexp_ir t.if_false acc5 env in
    let acc7 = (I.Goto l3) :: (I.Move {src = e2; dest = temp}) :: acc6 in 
    ((I.Label l3) :: acc7, I.Temp temp)
  | A.Fn_Call fn_call ->
    (* This should not be called for standalone fn call statement *)
    let fold_params (acc', args) mexp = 
      let (acc'', arg) = amexp_ir mexp acc' env in
      (acc'', arg :: args)
    in
    let (acc', arg_list_rev) = 
      List.fold ~f:fold_params ~init:(acc, []) fn_call.arg_list
    in
    let name = translate_name fn_call.ident env.gdecl_ctxts.fdecl_ctxt in
    let arg_list = List.rev arg_list_rev in
    let dest : As.sized_temp = 
      { temp = Temp.create () ; size = (type_opsize env.gdecl_ctxts.typedef_ctxt amexp.type_) } in
    let fn_call' = I.Fn_Call { name ; arg_list ; dest = Some dest } in
    (fn_call' :: acc', I.Temp dest)
  | A.Null -> (acc, I.Const64 Int64.zero)
  | A.Field_acc f -> 
    let (acc1,e) = lvalue_addr_ir f.struct_ acc env in
    let s_t_name = (match f.struct_.type_ with 
      | Struct t -> t 
      | _ -> failwith "expected struct typed expression") 
    in
    let (offset,typ) = SHT.find_exn ((SHT.find_exn env.structs_info s_t_name).flds_info) f.field in
    let t1 : As.sized_temp = { temp = Temp.create () ; size = As.S_64 } in
    let acc2 = (I.Field_acc_addr { struct_ = e ; offset = offset ; dest = t1}) :: acc1 in
    let t2 : As.sized_temp = 
      { temp = Temp.create () ; size = type_opsize env.gdecl_ctxts.typedef_ctxt typ } in
    let acc3 = (I.Unchecked_read { src = Temp t1 ; dest = t2 }) :: acc2 in
    (acc3, I.Temp t2)
  | A.Arr_acc a -> 
    let (acc1,e1) = amexp_ir a.arr acc env in 
    let (acc2,e2) = amexp_ir a.index acc1 env in
    let t : As.sized_temp = { temp = Temp.create () ; size = As.S_64 } in
    let elem_type_ =
      match a.arr.type_ with
      | A.Arr t -> t
      | _ -> failwith "Expected array to have array type"
    in
    let acc3 = 
      I.Arr_acc_addr 
        { arr = e1 
        ; typ_size = type_size env.gdecl_ctxts.typedef_ctxt env.structs_info elem_type_
        ; index = e2 ; dest = t } :: acc2 in
    let arr_typ = (match a.arr.type_ with
      | Arr elem_type -> elem_type
      | _ -> failwith "expected array to be of array type (my preconception could be wrong)")
    in
    (match arr_typ with
    | Struct _ -> (acc3, I.Temp t)
    | _ -> 
      let typ_size = type_opsize env.gdecl_ctxts.typedef_ctxt arr_typ in
      let t2 : As.sized_temp = { temp = Temp.create () ; size = typ_size } in 
      let acc4 = (I.Unchecked_read { src = Temp t ; dest = t2}) :: acc3 in 
      (acc4,I.Temp t2))
  | A.Pointer_dref p -> 
    let (acc1,e) = amexp_ir p acc env in
    let type_ =
      match p.type_ with
      | A.Ptr t -> t
      | _ ->
        sprintf "Expected a dereference of a pointer type, but got '%s' instead"
          (A.Print.pp_type p.type_)
        |> failwith
    in
    let t : As.sized_temp = 
      { temp = Temp.create () ; size = type_opsize env.gdecl_ctxts.typedef_ctxt type_} in 
    let acc2 = (I.Checked_read { src = e ; dest = t }) :: acc1 in 
    (acc2, I.Temp t)
  | A.Alloc a ->
    let typ_size =  type_size env.gdecl_ctxts.typedef_ctxt env.structs_info a in
    let t : As.sized_temp = { temp = Temp.create () ; size = As.S_64 } in 
    let acc1 = (I.Alloc { typ_size = typ_size ; dest = t }) :: acc in 
    (acc1, I.Temp t)
  | A.Alloc_arr a -> 
    let typ_size =  type_size env.gdecl_ctxts.typedef_ctxt env.structs_info a.type_ in
    let (acc1, e) = amexp_ir a.size acc env in
    let t : As.sized_temp = { temp = Temp.create () ; size = As.S_64 } in 
    let acc2 = (I.Alloc_arr { typ_size = typ_size ; count = e ; dest = t}) :: acc1 in 
    (acc2, I.Temp t)
    (* Calculates the address in an lvalue expression. Other than lvalue, is used for struct address
       calculation *)
and lvalue_addr_ir (lvalue : A.annotated_mexp) (acc : I.command list) (env : env) 
    : (I.command list * I.exp_pure) = 
    (match Mark.data lvalue.mexp with
    | A.Field_acc f -> 
      let (acc1,e) = lvalue_addr_ir f.struct_ acc env in 
      let s_t_name =
      (match f.struct_.type_ with 
      | Struct t -> t 
      | _ ->
        sprintf "expected struct typed expression, but got `%s`"
          (A.Print.pp_type f.struct_.type_)
        |> failwith) 
      in
      let (offset,_) = SHT.find_exn ((SHT.find_exn env.structs_info s_t_name).flds_info) f.field in
      let t : As.sized_temp = { temp = Temp.create () ; size = As.S_64 } in
      let acc2 = (I.Field_acc_addr { struct_ = e ; offset = offset ; dest = t}) :: acc1 in
      (acc2, I.Temp t)
    | A.Pointer_dref p -> 
      let (acc1,e) = amexp_ir p acc env in 
      (match e with
      | Temp _ -> (acc1,e)
      | _ -> failwith "calculated address should always be in a temp")
    | A.Arr_acc a -> 
      let (acc1,e1) = amexp_ir a.arr acc env in 
      let (acc2,e2) = amexp_ir a.index acc1 env in
      let t : As.sized_temp = { temp = Temp.create () ; size = As.S_64 } in
      let elem_type =
        match a.arr.type_ with
        | A.Arr t -> t
        | _ -> failwith "Expected array access to have array type"
      in
      let acc3 = 
        I.Arr_acc_addr 
          { arr = e1 
          ; typ_size = type_size env.gdecl_ctxts.typedef_ctxt env.structs_info elem_type
          ; index = e2 ; dest = t } :: acc2 in
      (acc3, I.Temp t)
    | A.Var v -> (acc, I.Temp (S.find_exn env.sym2temp v))
    | _ -> sprintf "Not valid lvalue type: (%s, %s)" 
      (A.Print.pp_type lvalue.type_) (A.Print.pp_exp (Mark.data lvalue.mexp))
      |> failwith)
and bool_jmp_ir 
  (b : A.mexp) (l1 : I.label) (l2 : I.label) (acc : I.command list) (env : env) : I.command list = 

  match Mark.data b with
  | True -> (I.Goto l1) :: acc
  | False -> (I.Goto l2) :: acc
  | Var v -> (I.If {lhs = I.Temp (S.find_exn env.sym2temp v); 
                    op = I.EqualsTo; 
                    rhs = I.Const32 Int32.one;
                    tru = l1; fls = l2}) :: acc
  | Comp c -> 
    let (acc1, e1) = amexp_ir c.lhs acc env in 
    let (acc2, e2) = amexp_ir c.rhs acc1 env in 
    (I.If {lhs = e1; op = binop_comp_ir c.op; rhs = e2; tru = l1; fls = l2}) :: acc2
  | Bang b -> abool_jmp_ir b l2 l1 acc env
  | Ternary t -> 
    let l3 = Local_label.create () in let l4 = Local_label.create () in
    let acc1 = abool_jmp_ir t.cond l3 l4 acc env in 
    let acc2 = (I.Label l3) :: acc1 in
    let acc3 = abool_jmp_ir t.if_true l1 l2 acc2 env in 
    let acc4 = (I.Label l4) :: acc3 in
    abool_jmp_ir t.if_false l1 l2 acc4 env
  | Fn_Call _ | Pointer_dref _ | Arr_acc _ | Field_acc _ ->
    let (acc1, cond_dest) = amexp_ir {mexp = b ; type_ = A.Bool} acc env in
    I.If { lhs = cond_dest
         ; op = I.EqualsTo
         ; rhs = I.Const32 (Int32.of_int_exn 1)
         ; tru = l1
         ; fls = l2 }
    :: acc1
  | Const _ | Pure _ | Impure _ | Null | Alloc _ | Alloc_arr _
    -> failwith "Not a boolean expression"

and abool_jmp_ir 
  (ab : A.annotated_mexp) (l1 : I.label) (l2 : I.label) (acc : I.command list) (env : env) 
    : I.command list = 
  bool_jmp_ir ab.mexp l1 l2 acc env

  
let rec mstm_ir (mstm : A.mstm) (acc : I.command list) (env : env) : I.command list = 
  match Mark.data mstm with 
  | A.Declare d ->
    if String.is_prefix (Symbol.name d.sym) ~prefix:"$TEMP" then 
      (match Mark.data d.mstm with
      | A.Block (asn1 :: decl1 :: _) -> 
        (match Mark.data decl1 with
        | A.Declare decl1_record -> (match Mark.data decl1_record.mstm with
          | A.Block (_ :: block1 :: _) -> 
            let asn_exp = (match Mark.data asn1 with 
            | A.Assign a -> a.amexp | _ ->
              failwith "Declare de-elaboration failure 3: exp value")
            in
            let orig_symbol = (match Mark.data decl1 with
            | A.Declare a -> a.sym | _ ->
              failwith "Declare de-elaboration failure 4: orig sym name")
            in
          let (acc1,e) = amexp_ir asn_exp acc env in 
          let newTemp : As.sized_temp =
            { temp = Temp.create ()
            ; size = 
              (match e with 
              | Temp t -> t.size 
              | Const64 _ -> As.S_64
              | _ -> As.S_32 ) }
          in
          let env1  =
            { env with sym2temp = (S.add_exn env.sym2temp ~key:orig_symbol ~data:newTemp) }
          in 
          let acc2 = (I.Move {src = e ; dest = newTemp}) :: acc1 in
          mstm_ir (block1) acc2 env1
          | _ -> failwith "Declare de-elaboration failure 3: block 2")
        | _ -> failwith "Declare de-elaboration failure 2: first decl")
      | _ -> failwith "Declare de-elaboration failure: block 1")
    else
      let sym2temp' =
        S.add_exn env.sym2temp ~key:d.sym 
          ~data:{ temp = Temp.create () ; size = type_opsize env.gdecl_ctxts.typedef_ctxt d.type_ }
      in
      mstm_ir d.mstm acc { env with sym2temp = sym2temp' }
  | A.Assign a -> 
    let elab_lhs_val asn_dest acc env = 
      let e_type = a.amexp.type_ in
      (match Mark.data a.lvalue.mexp with
      | A.Arr_acc _ | A.Field_acc _ -> 
        let t : As.sized_temp = 
          { temp = Temp.create () ; size = type_opsize env.gdecl_ctxts.typedef_ctxt e_type } in
        let acc1 = (I.Unchecked_read { src = asn_dest ; dest = t }) :: acc in
        (acc1, I.Temp t)
      | A.Pointer_dref _ -> 
        let t : As.sized_temp = 
          { temp = Temp.create () ; size = type_opsize env.gdecl_ctxts.typedef_ctxt e_type } in
        let acc1 = (I.Checked_read { src = asn_dest ; dest = t }) :: acc in
        (acc1, I.Temp t)
      | A.Var _ -> (acc,asn_dest)
      | _ -> failwith "invalid lvalue type") 
    in
    let pure_elab asn_dest op acc env = 
      let (acc1, rhs_val) = amexp_ir a.amexp acc env in
      let (acc2, lhs_val) = elab_lhs_val asn_dest acc1 env in
      (acc2, I.Binop_pure { lhs = lhs_val ; op = op ; rhs = rhs_val })
    in
    let impure_elab asn_dest op acc env = 
      let (acc1, rhs_val) = amexp_ir a.amexp acc env in
      let (acc2, lhs_val) = elab_lhs_val asn_dest acc1 env in
      let t : As.sized_temp = { temp = Temp.create () ; size = As.S_32 } in
      let acc3 = (I.Binop_impure { lhs = lhs_val ; op = op ; rhs = rhs_val ; dest = t }) :: acc2 in
      (acc3, I.Temp t)
    in

    let (acc1, asn_dest) = (match Mark.data a.lvalue.mexp with 
      | A.Var v -> (acc, I.Temp (S.find_exn env.sym2temp v))
      | _ -> lvalue_addr_ir a.lvalue acc env) in 
    let (acc2, asn_src) = (match a.asop with 
      | AEquals -> amexp_ir a.amexp acc1 env
      | APlus -> pure_elab asn_dest I.Plus acc1 env
      | AMinus -> pure_elab asn_dest I.Minus acc1 env
      | ATimes -> pure_elab asn_dest I.Times acc1 env
      | ADivided_by -> impure_elab asn_dest I.Divided_by acc1 env
      | AModulo -> impure_elab asn_dest I.Modulo acc1 env
      | ABWAnd -> pure_elab asn_dest I.BitwiseAnd acc1 env
      | ABWXor -> pure_elab asn_dest I.BitwiseXor acc1 env
      | ABWOr -> pure_elab asn_dest I.BitwiseOr acc1 env
      | ALShift -> impure_elab asn_dest I.LShift acc1 env
      | ARShift -> impure_elab asn_dest I.RShift acc1 env) in
    let dest_temp = (match asn_dest with 
      | I.Temp t -> t 
      | _ -> failwith "expected assignment dest to have temp type") in
    (match Mark.data a.lvalue.mexp with
    | A.Var _ -> (I.Move { src = asn_src ; dest = dest_temp }) :: acc2
    | A.Pointer_dref _ -> (I.Checked_write { src = asn_src ; dest = dest_temp }) :: acc2
    | _ -> (I.Unchecked_write { src = asn_src ; dest = dest_temp}) :: acc2)
  | A.If i -> 
    let l1 = Local_label.create () in
    let l2 = Local_label.create () in
    let l3 = Local_label.create () in 
    let acc1 = bool_jmp_ir i.cond.mexp l1 l2 acc env in
    let acc2 = (I.Label l1) :: acc1 in 
    let acc3 = mstm_ir i.if_true acc2 env in 
    let acc4 = (I.Goto l3) :: acc3 in 
    let acc5 = (I.Label l2) :: acc4 in 
    let acc6 = mstm_ir i.if_false acc5 env in
    let acc7 = (I.Goto l3) :: acc6 in
    (I.Label l3) :: acc7
  | A.While w -> 
    let guard1_lbl = Local_label.create () in
    let guard2_lbl = Local_label.create () in
    let body_lbl = Local_label.create () in
    let end_lbl = Local_label.create () in 
    let acc' = (I.Goto guard1_lbl) :: acc in
    let acc1 = (I.Label guard1_lbl) :: acc' in
    let acc2 = bool_jmp_ir w.guard.mexp body_lbl end_lbl acc1 env in
    let acc3 = (I.Label body_lbl) :: acc2 in 
    let acc4 = mstm_ir w.mstm acc3 env in 
    let acc5 = (I.Goto guard2_lbl) :: acc4 in
    let acc6 = (I.Label guard2_lbl) :: acc5 in
    let acc7 = bool_jmp_ir w.guard.mexp body_lbl end_lbl acc6 env in
    (I.Label end_lbl) :: acc7
  | A.Return ro -> (match ro with 
    | Some r -> let (acc1, e) = amexp_ir r acc env in (I.Return (Some e)) :: acc1
    | None -> (I.Return None) :: acc)
  | A.Block b -> mstms_ir b acc env
  | A.Expression e -> 
    (match Mark.data e.mexp with
    | A.Fn_Call c -> 
      (match (T.SHT.find_exn env.gdecl_ctxts.fdecl_ctxt c.ident).fdecl.ret_type with
      | None ->
        let fold_params (acc', args) mexp = 
          let (acc'', arg) = amexp_ir mexp acc' env in
          (acc'', arg :: args) in
        let (acc', arg_list_rev) = 
          List.fold ~f:fold_params ~init:(acc, []) c.arg_list
        in
        let name = translate_name c.ident env.gdecl_ctxts.fdecl_ctxt in
        let arg_list = List.rev arg_list_rev in
        let fn_call' = I.Fn_Call { name ; arg_list ; dest = None } in
        (fn_call' :: acc')
      | Some _ -> let (acc1,_) = amexp_ir e acc env in acc1)
    |_ -> let (acc1,_) = amexp_ir e acc env in acc1)
  | A.ABORT ->
    I.Fn_Call { name = Symbol.symbol "abort" ; arg_list = [] 
              ; dest = None} :: acc

and mstms_ir (mstms : A.mstm list) (acc : I.command list) (env : env) : I.command list = 
  match mstms with 
  | mstm :: mstms -> let acc1 = (mstm_ir mstm acc env) in (mstms_ir mstms acc1 env)
  | [] -> acc

let mgdecl_ir
    (gdecl_ctxts : T.gdecl_ctxts) (structs_info : struct_info SHT.t) (mgdecl : A.mgdecl) 
    (acc : I.command list): I.command list =
  match Mark.data mgdecl with
  | A.Fdecl _ -> acc
  | A.Fdefn fdefn ->
    let gen_temp_and_add_to_env (param_temps_rev, s2t) (param : A.type_ident) =
      let temp : As.sized_temp = 
        { temp = Temp.create () ; size = (type_opsize gdecl_ctxts.typedef_ctxt param.type_) } in
      (temp :: param_temps_rev, S.add_exn s2t ~key:param.ident ~data:temp)
    in
    let (param_temps_rev, sym2temp) = 
      List.fold ~init:([], S.empty) ~f:gen_temp_and_add_to_env fdefn.param_list
    in
    let name = translate_name fdefn.ident gdecl_ctxts.fdecl_ctxt in
    let param_temps = List.rev param_temps_rev in
    let ret_size_opt = (match (Option.value_exn (T.SHT.find (gdecl_ctxts.fdecl_ctxt) fdefn.ident)).fdecl.ret_type with 
      | Some t -> (match t with
        | A.Int | A.Bool -> Some Assem.S_32
        | A.Ptr _ | A.Arr _ -> Some Assem.S_64
        | A.Struct _ -> failwith "Large types should not be able to be returned by functions" 
        | A.Type_ident _ -> failwith "Fails if typedefs not fully unrolled"
        | A.Any_type -> failwith "Any type should never be returned")
      | None -> None) in
    let fn_label = I.Fn_Label { name ; param_temps ; ret_size_opt } in
    mstms_ir fdefn.block (fn_label :: acc) { sym2temp ; gdecl_ctxts ; structs_info} 
  | A.Typedef _ -> acc 
  | A.Sdefn s -> 
    let calc_offsets (acc : struct_info) (field : A.type_ident) = 
      let (size,align) = type_size_align gdecl_ctxts.typedef_ctxt structs_info field.type_ in
      (match align with
      | As.S_32 -> 
        SHT.add_exn acc.flds_info ~key:field.ident ~data:(acc.size,field.type_); 
        { acc with size = acc.size + size }
      | As.S_64 -> 
        let (curr0_size,_) as curr0 = (Int.round_up acc.size ~to_multiple_of:8, field.type_) in
        SHT.add_exn acc.flds_info ~key:field.ident ~data:curr0;
        { acc with size = curr0_size + size ; align = As.S_64 })
    in
    let s_info_unaligned =
      List.fold s.field_list 
        ~init:{ flds_info = SHT.create () ; size = 0; align = As.S_32} 
        ~f:calc_offsets
    in 
    let s_info = (match s_info_unaligned.align with 
    | As.S_32 -> s_info_unaligned
    | As.S_64 -> 
      { s_info_unaligned with size = Int.round_up s_info_unaligned.size ~to_multiple_of:8 })
    in
    SHT.add_exn structs_info ~key:s.ident ~data:s_info;
    acc


    
(* ------------------------------------ INTERFACE FUNCTION  ------------------------------------- *)

let translate (mgdecls : A.program) (gdecl_ctxts : T.gdecl_ctxts): I.program =
  let structs_info = SHT.create () in
  let rec translate_rev mgdecls acc =
    match mgdecls with
    | [] -> acc
    | mgdecl :: rest -> 
      translate_rev rest (mgdecl_ir gdecl_ctxts structs_info mgdecl acc)
  in
  translate_rev mgdecls [] |> List.rev

(* --------------------------------------- EXPECT TESTS  ---------------------------------------- *)

(* TODO: RIP expect test, maybe fix it at some point *)
(* let gen_masn ~lvalue ~asop ~amexp = A.Assign { lvalue ; asop ; amexp } |> Mark.naked
let gen_mret exp = A.Return exp |> Mark.naked
let gen_mconst c : A.annotated_mexp = { mexp = Int32.of_int_exn c |> A.Const |> Mark.naked ; type_ = Int }
let gen_mvar v type_ : A.annotated_mexp = { mexp = (A.Var v |> Mark.naked) ; type_ = type_ }
let gen_mfdefn ?t ~n ~ps ~b =
  A.Fdefn { ret_type = t ; ident = n ; param_list = ps ; block = b } |> Mark.naked

let%expect_test "Test ir translation of a program that calls a function foo from main." =
  Temp.reset ();
  let x : Symbol.t = Symbol.symbol "x" in
  let t = A.Int in
  let asn_exp = (A.Pure { lhs = gen_mvar x Int ; rhs = gen_mconst 10 ; op = Plus }) |> Mark.naked in
  let asn_amexp : A.annotated_mexp = { mexp = asn_exp ; type_ = Int } in
  let asn_and_ret = 
    let thing =  gen_masn ~lvalue:(gen_mvar x Int) ~asop:A.AEquals ~amexp:asn_amexp in
    let thing2 = gen_mret (Some (gen_mvar x Int)) in
    A.Block [thing;thing2] |> Mark.naked
  in
  let main_name = Symbol.symbol "main" in
  let f_name = Symbol.symbol "foo" in 
  let call = A.Fn_Call { ident = f_name ; arg_list = [gen_mconst 5] } |> Mark.naked in
  let acall : A.annotated_mexp = { mexp = call ; type_ = Int } in
  let call_and_ret = A.Block [ gen_mret (Some acall) ] |> Mark.naked in
  let ast_program = 
    A.[ gen_mfdefn ~t:Int ~n:f_name ~ps:[{ type_ = t ; ident = x }] ~b:[asn_and_ret]
      ; gen_mfdefn ~t:Int ~n:main_name ~ps:[] ~b:[call_and_ret] ]
  in
  (* let gdecl_ctxts = Typechecker.typecheck ast_program in *)
  let fdecl_ctxt : T.fdecl_status SHT.t = SHT.create () in
  SHT.add_exn (fdecl_ctxt) ~key:f_name 
    ~data:({ fdecl = { ret_type = Some(A.Int) 
                     ; ident = f_name 
                     ; param_list = [{ type_ = t ; ident = x }] 
                     ; extern = false } 
           ; init_status = Init 
           ; used = true });
  SHT.add_exn (fdecl_ctxt) ~key:main_name 
    ~data:({ fdecl = { ret_type = Some(A.Int) 
                     ; ident = main_name 
                     ; param_list = [] 
                     ; extern = false } 
           ; init_status = Init 
           ; used = true });
  let gdecl_ctxts : T.gdecl_ctxts = { fdecl_ctxt = fdecl_ctxt ; typedef_ctxt = SHT.create () } in

  let ir_program = translate ast_program gdecl_ctxts in
  prerr_endline (I.Print.pp_program ir_program);
  [%expect
    {|
    ._c0_foo(%t1_S_32):
    	%t1_S_32 <- (%t1_S_32) + (10)
    	return %t1_S_32
    ._c0_main():
    	%t2 <- _c0_foo(5)
    	return %t2_S_32
  |}]
;;
 *)
