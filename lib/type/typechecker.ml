(* L4 Compiler
 * Semantic Analysis and Type Annotation 
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Elan Biswas <elanb@andrew.cmu.edu> and Giancarlo Zaniolo <gzaniolo@andrew.cmu.edu>
 *
 * Performs semantic analysis checks necessary to ensure that the input L4 program is well-formed.
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now distinguishes between declarations and initialization
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Should be more up-to-date with modern spec.
 * Modified: Matt Bryant <mbryant@andrew.cmu.edu> Fall 2015
 * Handles undefined variables in unreachable code, significant simplifications
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu> Fall 2018
 *   Use records, redo marks.
 *)


open Core


module A = Ast
module SM = Symbol.Map
module SS = Symbol.Set
module SH = Hash_set.Make(Symbol)
module SHT = Hashtbl.Make(Symbol) 

type init_status =
  | Decl
  | Init
type type_status = (init_status * A.type_)

type fdecl_status = 
  { fdecl : A.fdecl
  ; init_status : init_status
  ; used : bool
  }

type struct_context_t = (A.type_ SHT.t) SHT.t
type function_context_t = fdecl_status SHT.t 
type typedef_context_t = A.type_ SHT.t

type env =
  { vars : (type_status) SM.t
  ; returns : bool
  ; return_type : A.ret_type
  ; fn_ctxt : function_context_t
  ; td_ctxt : typedef_context_t
  ; sd_ctxt : struct_context_t
  }

type gdecl_ctxts = 
  { fdecl_ctxt : function_context_t
  ; typedef_ctxt :typedef_context_t }

let rec unroll_tdef td_ctxt = function
  | A.Type_ident i -> SHT.find_exn td_ctxt i
  | A.Ptr t -> unroll_tdef td_ctxt t |> A.Ptr
  | A.Arr t -> unroll_tdef td_ctxt t |> A.Arr
  | t -> t
;;

let eq_type_ td_ctxt t1 t2 = 
  let t1v = unroll_tdef td_ctxt t1 in
  let t2v = unroll_tdef td_ctxt t2 in
  match (t1v, t2v) with
  | (A.Ptr A.Any_type, A.Ptr _) | (A.Ptr _, A.Ptr A.Any_type) -> true
  | _ -> A.equal_type_ t1v t2v
;;

let find_type_exn (error : msg:string -> 'a) (td_ctxt : typedef_context_t) (t : A.type_) =
  try unroll_tdef td_ctxt t
  with _ -> error ~msg:(sprintf "Type %s does not exist" (A.Print.pp_type t))

let check_if_type_defn'd (error : msg:string -> 'a) (td_ctxt : typedef_context_t) (t : A.type_) = 
  let _ : A.type_ = find_type_exn error td_ctxt t in ()

let check_sym_not_type_defn'd
    (error : msg:string -> 'a) (td_ctxt : typedef_context_t) (s : Symbol.t) =
(match SHT.find td_ctxt s with
| Some _ -> error 
  ~msg:(sprintf "Symbol cannot have the same name as typedef: `%s" (Symbol.name s))
| None -> ())


(* ------------------------------ BEGIN HELPERS FOR ERROR MESSAGES ------------------------------ *)

let tc_errors : Error_msg.t = Error_msg.create ()

let gen_error m ~msg = 
  Error_msg.error tc_errors (Mark.src_span m) ~msg;
  raise Error_msg.Error
(* ------------------------------- END HELPERS FOR ERROR MESSAGES ------------------------------- *)

(* remark marked a ==> A mark with the same span of marked and data a  *)
let remark marked a = Mark.map ~f:(fun _ -> a) marked ;;

let is_struct = function | A.Struct _ -> true | _ -> false
;;
let check_small_type error td_ctxt t =
  if is_struct (unroll_tdef td_ctxt t) then
    error ~msg:"Expected a small type, but got a large type instead"
;;
let check_struct_is_def error (sd_ctxt : struct_context_t) (struct_name : Symbol.t) =
  if not (SHT.mem sd_ctxt struct_name) then
    error ~msg:(sprintf "`struct %s` not defined before use" (Symbol.name struct_name))
;;

let annotate mexp type_ : A.annotated_mexp = { mexp ; type_ } 

let rec tc_exp (ast : A.mexp) (env : env) (type_ : A.type_) : A.annotated_mexp =
  let error = gen_error ast in
  let error_act_type act =
    error ~msg:(sprintf "Expected: %s. Actual: %s" (A.Print.pp_type type_) (A.Print.pp_type act))
  in
  let if_neq_err act = if (eq_type_ env.td_ctxt type_ act) then () else error_act_type act in 
  let ast' = tc_synth_exp ast env in
  ast'.type_ |> if_neq_err ;
  ast'
and tc_synth_exp (ast : A.mexp) (env : env) : A.annotated_mexp = 
  let error = gen_error ast in
  let check_struct_is_def_err = check_struct_is_def error env.sd_ctxt in
  let rec get_struct_name (t : A.type_) : Symbol.t =
    match t with
    | A.Struct s -> s
    | A.Type_ident sym -> SHT.find_exn env.td_ctxt sym |> get_struct_name 
    | Int | Bool | Any_type | Ptr _ | Arr _ ->
      error 
        ~msg:(sprintf "Expected an expression of type struct. Instead got expression of type `%s`"
          (A.Print.pp_type t))
  in
  match Mark.data ast with
  | A.True ->  annotate ast A.Bool
  | A.False -> annotate ast A.Bool
  | A.Const _ -> annotate ast A.Int 
  | A.Var id ->
    (match SM.find env.vars id with
    | None -> error ~msg:(sprintf "Not declared before use: `%s`" (Symbol.name id))
    | Some (Decl,_) -> error ~msg:(sprintf "Not initialized before use: `%s`" (Symbol.name id))
    | Some (Init, t) -> annotate ast t)
  | A.Null -> annotate ast (A.Ptr A.Any_type)
  | A.Pure binop ->
    let lhs = tc_exp binop.lhs.mexp env A.Int in
    let rhs = tc_exp binop.rhs.mexp env A.Int in
    let ast' = A.Pure { binop with lhs ; rhs } |> remark ast in
    annotate ast' A.Int
  | A.Impure binop ->
    let lhs = tc_exp binop.lhs.mexp env A.Int in
    let rhs = tc_exp binop.rhs.mexp env A.Int in
    let ast' = A.Impure {binop with lhs ; rhs } |> remark ast in
    annotate ast' A.Int
  | A.Fn_Call fn ->
    let (arg_list, f_decl) = tc_call_synth_fdecl_and_args ast env in
    (match f_decl.ret_type with
    | Some t ->
      let ast' = A.Fn_Call { fn with arg_list } |> remark ast in
      annotate ast' t
    | None -> 
      error ~msg:(sprintf 
        "Invalid function call: `%s`. Void functions can only be called as top-level expressions."
        (Symbol.name fn.ident)))
  | A.Comp cmp -> (match cmp.op with
    | A.EqualsTo | A.NotEqualsTo ->
        let lhs = tc_synth_exp cmp.lhs.mexp env in
        let rhs = tc_synth_exp cmp.rhs.mexp env in
        let ast' = A.Comp { cmp with lhs ; rhs } |> remark ast in
        (* We don't need to check the other type because it should be equal *)
        check_small_type error env.td_ctxt lhs.type_ ;
        (if eq_type_ env.td_ctxt lhs.type_ rhs.type_ then annotate ast' A.Bool 
         else error ~msg:("Left-hand side and right-hand side of operator do not have matching" 
                          ^ " types."))
    | A.LessThan | A.LessThanEq | A.GreaterThan | A.GreaterThanEq ->
        let lhs = tc_exp cmp.lhs.mexp env A.Int in
        let rhs = tc_exp cmp.rhs.mexp env A.Int in
        let ast' = A.Comp { cmp with lhs ; rhs } |> remark ast in
        annotate ast' A.Bool)
  | A.Bang amexp -> 
    let mexp = tc_exp amexp.mexp env A.Bool in
    let ast' = A.Bang mexp |> remark ast in
    annotate ast' A.Bool 
  | A.Ternary t ->
    let cond = tc_exp t.cond.mexp env A.Bool in
    let if_true = tc_synth_exp t.if_true.mexp env in
    let if_false = tc_synth_exp t.if_false.mexp env in
    let t1 = if_true.type_ in
    let t2 = if_false.type_ in
    (* We don't need to check the other type because it should be equal *)
    check_small_type error env.td_ctxt if_true.type_ ;
    (if not (eq_type_ env.td_ctxt t1 t2) then
      error ~msg:"Ternary expressions do not have matching types") ;
    (match (unroll_tdef env.td_ctxt t1, unroll_tdef env.td_ctxt t2) with
    | (A.Ptr A.Any_type, t) | (t, A.Ptr A.Any_type) | (t, _) ->
      let ast' = A.Ternary { cond ; if_true ; if_false } |> remark ast in
      annotate ast' t)
  | A.Field_acc f ->
    let struct_ : A.annotated_mexp = tc_synth_exp f.struct_.mexp env in
    let struct_name = get_struct_name struct_.type_ in
    check_struct_is_def_err struct_name ;
    let field_infos = SHT.find_exn env.sd_ctxt struct_name in
    let field_info_op = SHT.find field_infos f.field in
    (match field_info_op with
    | None ->
      error ~msg:(sprintf "`struct %s` has no field `%s`"
        (Symbol.name struct_name) (Symbol.name f.field))
    | Some t ->
      let ast' = A.Field_acc { f with struct_ } |> remark ast in
      annotate ast' t)
  | A.Alloc type_ ->
    if unroll_tdef env.td_ctxt type_ |> is_struct then
      get_struct_name type_ |> check_struct_is_def_err ;
    annotate ast (A.Ptr type_)
  | A.Alloc_arr type_size ->
    let t = unroll_tdef env.td_ctxt type_size.type_ in
    let size = type_size.size in
    if is_struct t then get_struct_name t |> check_struct_is_def_err ;
    let size' = tc_exp size.mexp env A.Int in
    let ast' = A.Alloc_arr { type_size with size = size' } |> remark ast in
    annotate ast' (A.Arr type_size.type_)
  | A.Pointer_dref amexp ->
    let amexp' = tc_synth_exp amexp.mexp env in
    let t_star = amexp'.type_ in
    (match (unroll_tdef env.td_ctxt t_star) with
    | A.Ptr Any_type -> error ~msg:"Cannot dereference NULL"
    | A.Ptr t ->
      let ast' = A.Pointer_dref amexp' |> remark ast in
      annotate ast' t
    | _ ->
        error
          ~msg:(sprintf "Attempted to dereference non-pointer expression with type `%s`"
            (A.Print.pp_type t_star)))
  | A.Arr_acc arr_index -> 
    let index = tc_exp arr_index.index.mexp env A.Int in
    let arr = tc_synth_exp arr_index.arr.mexp env in
    (match unroll_tdef env.td_ctxt arr.type_ with
    | A.Arr t ->
      let ast' = A.Arr_acc { arr ; index } |> remark ast in
      annotate ast' t
    | _ -> error ~msg:"Attempted an array access on non-array" )
  
and tc_call_synth_fdecl_and_args 
    (fn_call : A.mexp) (env : env) : (A.annotated_mexp list * A.fdecl) =
  match Mark.data fn_call with
  | A.Fn_Call fn ->
      let error = gen_error fn_call in
      let f_decl = 
      (match SHT.find env.fn_ctxt fn.ident with
      | None -> error ~msg:(sprintf "Function not declared before use: `%s`" (Symbol.name fn.ident))
      | Some fn_ctxt_r -> 
        SHT.set env.fn_ctxt ~key:fn.ident ~data:{fn_ctxt_r with used = true};
        fn_ctxt_r.fdecl)
      in
      let fn_name = Symbol.name fn.ident in
      let length_check = 
      ( match SM.find env.vars f_decl.ident with 
      | Some _ -> 
        error ~msg:(sprintf "Variable with same name as function already in scope: `%s`" fn_name)
      | None ->
        let check_one (a : A.annotated_mexp) (b : A.type_ident) : A.annotated_mexp =
          tc_exp a.mexp env b.type_
        in 
        List.map2 ~f:check_one fn.arg_list f_decl.param_list )
      in
      (match length_check with
      | Ok arg_list -> ( arg_list, f_decl )
      | Unequal_lengths ->
        error
          ~msg:(sprintf "Number of arguments does not match previous declaration: `%s`" fn_name)) ;
  | _ -> failwith "Expected a function call"
;;

let rec check_is_lval (error : msg:string -> unit) (exp : A.exp) =
  match exp with
  | A.Var _ -> ()
  | A.Field_acc fa -> Mark.data fa.struct_.mexp |> check_is_lval error
  | A.Pointer_dref pd -> Mark.data pd.mexp |> check_is_lval error
  | A.Arr_acc aa -> Mark.data aa.arr.mexp |> check_is_lval error
  | A.Const _ | A.True | A.False | A.Null | A.Pure _ | A.Impure _ | A.Fn_Call _ | A.Comp _
  | A.Bang _ | A.Ternary _ | A.Alloc _ | A.Alloc_arr _ ->
      error ~msg:(sprintf "Expected an lvalue. Got `%s` instead" (A.Print.pp_exp exp))
;;
let tc_synth_lval (mlval : A.mexp) (env : env) : A.annotated_mexp =
  let error = gen_error mlval in
  let lval = Mark.data mlval in
  check_is_lval error lval ;
  match lval with
  | A.Var sym -> 
    (match SM.find env.vars sym with
    | Some (_, t) -> annotate mlval t
    | None -> error ~msg:(sprintf "Not declared before initialization: `%s`" (Symbol.name sym)))
  | _ -> tc_synth_exp mlval env

(* tc_stm ast env
 *   env.vars: environment under which to consider the ast, where:
 *     find env.vars id = Some (Decl,t) if id is declared but not initialized, with type t
 *     find env.vars id = None if id is not declared or initialized
 *     find env.vars id = Some (Init,t) if id is declared and initialized, with type t
 *
 *   env.fn_ctxt:
 *      find env.fn_ctxt id = Some status if the function has been declared
 *        status.fdecl = a declaration representing the funciton
 *        status.init_status = Decl if the function has not been initialized
 *        status.init_status = Init if the function has been initialized
 *        used = true iff the function has been called
 *      find env.fn_ctxt id = None if the function has not been declared or initialized
 *
 *   env.td_ctxt:
 *      find env.td_ctxt id = Some t if id has been typedefined to a type that resolves to type t
 *      find env.td_ctxt id = None if id has not been typedefined
 *
 *   env.sd_ctxt
 *      find env.sd_ctxt id = Some m if struct id has been defined. m is a map of field names to
 *                                   types
 *      find env.sd_ctxt id = None if struct id has not been defined.
 *
 *   env.returns
 *     whether the previous statements returned.
 *
 *   ast: The (misnamed) statement to typecheck.
 *)
let rec tc_mstm (ast : A.mstm) (env : env) : (A.mstm * env) =
  let error ~msg =
    Error_msg.error tc_errors (Mark.src_span ast) ~msg;
    raise Error_msg.Error
  in match Mark.data ast with
  | A.Declare d -> 
    let var_type = unroll_tdef env.td_ctxt d.type_ in
    check_sym_not_type_defn'd error env.td_ctxt d.sym;
    check_small_type error env.td_ctxt d.type_ ;
    (match SM.find env.vars d.sym with
    | Some _ -> error ~msg:(sprintf "Already declared: `%s`" (Symbol.name d.sym))
    | None ->
      let (d_mstm', env') =
        tc_mstm d.mstm { env with vars = SM.set env.vars ~key:d.sym ~data:(Decl, var_type) } 
      in
      let merge_hlpr ~key b = 
        (match b with
        | `Both (_, curr) -> Some curr 
        | `Left _ ->
          sprintf "Variable `%s` becomes undeclared in scope of `%s`:\n%s"
            (Symbol.name key) (Symbol.name d.sym) (A.Print.pp_stm (Mark.data d.mstm))
          |> failwith
        | `Right _ -> None)
      in
      let vars' = SM.merge env.vars env'.vars ~f:merge_hlpr in
      let ast' = A.Declare { d with mstm = d_mstm' } |> remark ast in
      (ast', { env with vars = vars'; returns = env'.returns }))
  | A.Assign asn ->
    let lvalue = 
      (match asn.asop with
      | A.AEquals ->
        let lvalue = tc_synth_lval asn.lvalue.mexp env in
        check_small_type error env.td_ctxt lvalue.type_ ;
        lvalue
      | A.APlus | A.AMinus | A.ATimes | A.ADivided_by | A.AModulo | A.ABWAnd | A.ABWXor | A.ABWOr
      | A.ALShift | A.ARShift ->
        check_is_lval error (Mark.data asn.lvalue.mexp);
        let lvalue = tc_exp asn.lvalue.mexp env A.Int in
        lvalue )
    in
    let amexp = tc_exp asn.amexp.mexp env lvalue.type_ in
    let ast' = A.Assign { asn with lvalue ; amexp } |> remark ast in
    (match Mark.data asn.lvalue.mexp with
    | A.Var sym -> (* Judgements say to check if var name = typedef, but will already fail *)
      let vars' = SM.set env.vars ~key:sym ~data:(Init, lvalue.type_) in
      (ast', { env with vars = vars' ; returns = false })
    | _ ->
      (ast', { env with returns = false }))
  | A.If i ->
    let cond = tc_exp i.cond.mexp env A.Bool in
    let (if_true, env1) = tc_mstm i.if_true env in
    let (if_false, env2) = tc_mstm i.if_false env in
    let intersect_inits ~key = function 
    | `Both ((Init, t),(Init, _)) -> let _ = key in Some (Init, t) 
    | `Both ((_, t), _) | `Right (_, t) | `Left (_ ,t) -> 
      if SM.mem env.vars key then Some (Decl, t) else None
    in 
    let vars = SM.merge env1.vars env2.vars ~f:intersect_inits in
    let returns = env1.returns && env2.returns in
    let ast' = A.If { cond ; if_true ; if_false } |> remark ast in
    (ast', { env with vars ; returns })
  | A.While w ->
    let guard = tc_exp w.guard.mexp env A.Bool in
    let (mstm, _) : A.mstm * env = tc_mstm w.mstm env in
    let ast' = A.While {guard ; mstm } |> remark ast in
    ( ast', { env with returns = false } )
  | A.Return eo ->
    let ast' =
      (match eo with
      | Some e ->
        (match env.return_type with
        | Some t -> tc_exp e.mexp env t |> Some |> A.Return |> remark ast
        | None -> error ~msg:"Void function cannot return an expression")
      | None -> 
        if Option.equal (eq_type_ env.td_ctxt) None env.return_type then ast
        else error ~msg:"Function does not return void") in
    (* Define all variables declared before return *)
    let vars = SM.map env.vars ~f:(fun (_,t) -> (Init,t)) in
    ( ast', { env with vars ; returns = true } )
  | A.Block [] | A.ABORT -> (ast, env)
  | A.Block (mstms) -> 
    let (mstms', env') = tc_mstms mstms env in
    let ast' = A.Block mstms' |> remark ast in
    ( ast', env' )
  | A.Expression ae ->
    let e = ae.mexp in
    let ast' =
    (match Mark.data e with
    | A.Fn_Call fn ->
      let (arg_list, fdecl) = tc_call_synth_fdecl_and_args e env in
      let e' = A.Fn_Call { fn with arg_list } |> remark e in
      let type_ = (match fdecl.ret_type with Some t -> t | None -> A.Int) in
      let ast' = A.Expression { mexp = e' ; type_ } |> remark ast in
      ast'
    | _ ->
      let ae' = tc_synth_exp e env in 
      check_small_type error env.td_ctxt ae'.type_ ;
      A.Expression ae' |> remark ast ) in
    ( ast', { env with returns = false } )
  and tc_mstms (mstms : A.mstm list) (env : env) : (A.mstm list * env) = 
    let aggregate_env acc a =
      let (mstms', env') = acc in
      let (a', env_a) = tc_mstm a env' in
      (* NOTE: before merging init_vars & decl_vars, line below only set init_vars *)
      (a' :: mstms', { env' with vars = env_a.vars ; returns = env_a.returns || env'.returns })
    in
    let (rev_mstms, env') = List.fold mstms ~init:([], env) ~f:aggregate_env in
    (List.rev rev_mstms, env')
;;

let tc_mgdecl 
    (mgdecl :  A.mgdecl)
    (fn_ctxt : function_context_t)
    (td_ctxt : typedef_context_t)
    (sd_ctxt : struct_context_t)
    : A.mgdecl = 
  let error ~msg = 
    Error_msg.error tc_errors (Mark.src_span mgdecl) ~msg;
    raise Error_msg.Error
  in
  let type_idents_contains_dup =
    Fn.compose
      (List.contains_dup ~compare:Symbol.compare)
      (List.map ~f:(fun (p : A.type_ident) -> p.ident))
  in
  let check_dup_params (fd : A.fdecl) : unit = 
    if type_idents_contains_dup fd.param_list then
      error ~msg:(sprintf "Duplicate `%s`" (Symbol.name fd.ident))
  in
  let check_param_names (fd : A.fdecl) : unit = 
    List.iter fd.param_list ~f:(fun param -> check_sym_not_type_defn'd error td_ctxt param.ident)
  in
  let check_param_types (params : A.type_ident list) : unit =
    let check_one (p : A.type_ident) =
      check_small_type error td_ctxt p.type_ ;
    in
    List.iter params ~f:check_one
  in
  let chk_param_n_ret_types_n_redecl_n_td (fd : A.fdecl) (init_status : init_status) 
    : unit =
    let check_one_param (in_el : A.type_ident) (ex_el : A.type_ident) = 
      if (eq_type_ td_ctxt in_el.type_ ex_el.type_) then ()
      else 
        error 
          ~msg:(sprintf "Parameter has a different type than initial function declaration: `%s`"
            (Symbol.name in_el.ident)) 
    in
    let check_param_types (input : A.fdecl) (existing : A.fdecl) = 
      List.iter2 input.param_list existing.param_list ~f:check_one_param
    in
    let check_return_types (input : A.fdecl) (existing : A.fdecl) = 
      if (Option.equal (eq_type_ td_ctxt) input.ret_type existing.ret_type) then ()
      else
        error
          ~msg:(sprintf
            "Return type of this function does not match original declaration: `%s`"
            (Symbol.name fd.ident))
    in
    check_sym_not_type_defn'd error td_ctxt fd.ident;
    (match SHT.find fn_ctxt fd.ident with
    | None -> let new_status = if fd.extern then Init else init_status in
      List.iter fd.param_list 
      ~f:(fun param -> check_if_type_defn'd error td_ctxt param.type_);
      (match fd.ret_type with None -> () | Some t -> check_if_type_defn'd error td_ctxt t);
      SHT.add_exn fn_ctxt ~key:fd.ident ~data:{fdecl = fd ; init_status = new_status ; used = false}
    | Some fn_ctxt_r -> 
      (match check_param_types fd fn_ctxt_r.fdecl with 
      | Unequal_lengths -> 
        error 
          ~msg:(sprintf
            "Number of arguments for this function does not match previous definition: `%s`"
            (Symbol.name fd.ident))
      | Ok _ -> 
        check_return_types fd fn_ctxt_r.fdecl;
        (match (init_status, fn_ctxt_r.init_status) with
        | (Decl, _) ->
          let new_status = if fd.extern then Init else fn_ctxt_r.init_status in
          SHT.update fn_ctxt fd.ident ~f:(fun _ -> { fn_ctxt_r with init_status = new_status })
        | (Init, Decl) -> SHT.update fn_ctxt fd.ident 
          ~f:(fun _ -> { fn_ctxt_r with init_status = Init })
        | (Init, Init) -> 
              error ~msg:(sprintf "Cannot redefine a function: `%s`" (Symbol.name fd.ident)))))
  in
  let check_ret_small (ret_type : A.ret_type) : unit =
    Option.iter ret_type ~f:(check_small_type error td_ctxt)
  in
  let unroll_type (type_ident : A.type_ident) =
    { type_ident with type_ = unroll_tdef td_ctxt type_ident.type_ }
  in
  match Mark.data mgdecl with 
  | A.Fdecl fd ->
    check_param_names fd;
    check_param_types fd.param_list;
    check_dup_params fd;
    check_ret_small fd.ret_type;
    let param_list = List.map ~f:unroll_type fd.param_list in
    let ret_type = Option.map ~f:(unroll_tdef td_ctxt) fd.ret_type in
    let fd' = { fd with param_list ; ret_type } in
    if fd.extern && Symbol.(fd.ident = ( Symbol.symbol "main")) then
      error ~msg:("main function cannot appear in the header function.") ;
    chk_param_n_ret_types_n_redecl_n_td fd' Decl ;
    A.Fdecl fd' |> remark mgdecl
  | A.Fdefn fn -> 
    let param_list = List.map ~f:unroll_type fn.param_list in
    let ret_type = Option.map ~f:(unroll_tdef td_ctxt) fn.ret_type in
    let temp_fdecl : A.fdecl = 
      { ret_type ; ident = fn.ident ; param_list = param_list ; extern = false } 
    in
    check_param_names temp_fdecl;
    check_param_types fn.param_list;
    check_dup_params temp_fdecl;
    check_ret_small fn.ret_type;
    chk_param_n_ret_types_n_redecl_n_td temp_fdecl Init;
    let vars_0 = List.fold param_list ~init:(SM.empty) 
      ~f:(fun acc a -> SM.add_exn acc ~key:a.ident ~data:(Init,a.type_))
    in
    let env_0 = 
      { vars = vars_0
      ; returns = false
      ; return_type = ret_type
      ; fn_ctxt
      ; td_ctxt
      ; sd_ctxt }
    in 
    let (block, env_1) : A.mstm list * env = tc_mstms fn.block env_0 in 
    if env_1.returns then A.Fdefn { fn with block ; param_list ; ret_type } |> remark mgdecl
    else error ~msg:(sprintf "Function does not return: `%s`" (Symbol.name fn.ident))
  | A.Typedef td -> 
    (if SHT.mem fn_ctxt td.ident then
      error ~msg:(sprintf "Typedef conflicts with function name: `%s`" (Symbol.name td.ident))
    else 
      try SHT.add_exn td_ctxt ~key:td.ident ~data:(find_type_exn error td_ctxt td.type_) ; mgdecl
      with _ -> error ~msg:(sprintf "Conflicting typedefs: `%s`" (Symbol.name td.ident)))
  | A.Sdefn sd ->
    (if SHT.mem sd_ctxt sd.ident then
      error ~msg:(sprintf "Struct defined more than once: `%s`" (Symbol.name sd.ident)));
    (if type_idents_contains_dup sd.field_list then
        error ~msg:(sprintf "`struct %s` has duplicate field names" (Symbol.name sd.ident)));
    let field_info = SHT.create () in
    let update_finfo (f : A.type_ident) =
      let ft = unroll_tdef td_ctxt f.type_ in
      (match ft with | A.Struct s -> check_struct_is_def error sd_ctxt s | _ -> ()) ;
      SHT.add_exn field_info ~key:f.ident ~data:ft
    in
    (* The order of the following two checks matters because recursive structs are disallowed *)
    List.iter sd.field_list ~f:update_finfo ;
    SHT.add_exn sd_ctxt ~key:sd.ident ~data:field_info ;
    mgdecl


let tc_mgdecls
    (mgdecls : A.mgdecl list)
    (fn_ctxt : function_context_t)
    (td_ctxt : typedef_context_t)
    (sd_ctxt : struct_context_t)
    : A.mgdecl list= 
  List.map mgdecls ~f:(fun a -> tc_mgdecl a fn_ctxt td_ctxt sd_ctxt)

let typecheck (prog : A.program) : (A.program * gdecl_ctxts) = 
  let fn_ctxt : function_context_t = SHT.create () in
  let td_ctxt : typedef_context_t = SHT.create () in
  let sd_ctxt : struct_context_t = SHT.create () in
  let main_fdecl =
    { A.ret_type = Some A.Int 
    ; A.ident = (Symbol.symbol "main") 
    ; A.param_list = [] 
    ; A.extern = false
    }
  in
  SHT.add_exn
    fn_ctxt
    ~key:(Symbol.symbol "main") 
    ~data: { fdecl = main_fdecl ; init_status = Decl ; used = true };
  let prog' = tc_mgdecls prog fn_ctxt td_ctxt sd_ctxt in
  let fn_is_defined_exn (fs : fdecl_status) = 
  (match fs.init_status with
  | Decl -> if fs.used then  
    sprintf "Function is called but not defined: %s" (Symbol.name (fs.fdecl.ident)) |> failwith
    else ()
  | _ -> ()) in
  SHT.iter fn_ctxt ~f:fn_is_defined_exn ;
  (prog', { fdecl_ctxt = fn_ctxt ; typedef_ctxt = td_ctxt })

