(* Implementation of the x86 calling convention translation phase for the three-address pseudo-
 * Assembly.
 *
 * Updated to match l4 spec
 *)
open Core

module AS = Assem
module AL = Assem.Label
module STIR = AS.Stack_Temp_Imm_Reg
module QWT = AS.Quad_With_Temps
module CFG = Cfg

(* Match each parameter with its corresponding register or stack position according to the C ABI *)
let gen_args (param_temps : AS.sized_temp list)
    ~(int_size_to_stack_arg : int -> AS.x86_operand_size -> STIR.t) : STIR.t list =
  let rec gen_args_rev
    (remaining_params : AS.sized_temp list)
    (remaining_regs : AS.x86_reg_64 list)
    (stack_slots_used : int)
    (acc : STIR.t list) =
    match (remaining_params, remaining_regs) with
    | ([], _) -> acc
    | (t :: ts, []) ->
      let acc' = int_size_to_stack_arg stack_slots_used t.size :: acc in
      gen_args_rev ts remaining_regs (stack_slots_used + 1) acc'
    | (t :: ts, r :: rs) ->
      let acc' = STIR.Reg { reg = r ; size = t.size } :: acc in
      gen_args_rev ts rs stack_slots_used acc'
  in
  gen_args_rev param_temps AS.x86_arg_regs 0 [] |> List.rev
;;

(* NOTE: This mutates the CFG *)
let translate (cfg : QWT.program CFG.t) : QWT.program CFG.t =
  let callee_save_srcs : STIR.t list ref  = ref [] in
  let callee_save_dests : STIR.t list ref = ref [] in
  let mov_args ~(srcs : STIR.t list) ~(dests : STIR.t list) =
    List.zip_exn srcs dests |> List.map ~f:(fun (src, dest) -> QWT.Mov { src ; dest })
  in
  let temps_to_operands temps = List.map ~f:(fun t -> STIR.Temp t) temps in
  let rec translate_block_acc (prog : QWT.program) (acc_rev : QWT.program) : QWT.instr list =
    match prog with
    | [] -> acc_rev
    | (QWT.Label (AL.Fn_label cur_fn)) :: rest ->
      let arg_dests = temps_to_operands cur_fn.param_temps in
      let arg_srcs =
        gen_args cur_fn.param_temps
          ~int_size_to_stack_arg:(fun i s -> STIR.Arg_In_Stack_Idx { idx = i ; size = s })
      in
      let arg_get_intrs =
        QWT.Label (AL.Fn_label cur_fn) :: (mov_args ~srcs:arg_srcs ~dests:arg_dests)
      in
      let acc_rev' = List.rev_append arg_get_intrs acc_rev in
      callee_save_dests :=
        (* We just assume that all callee saved can be treated as 64 bc idt it matters *)
        List.map AS.x86_callee_saved_regs
          ~f:(fun _ -> STIR.Temp { temp = Temp.create () ; size = AS.S_64 }) ;
      callee_save_srcs :=
        List.map ~f:(fun r -> STIR.Reg { reg = r ; size = AS.S_64 }) AS.x86_callee_saved_regs ;
      let callee_save_instrs = mov_args ~srcs:!callee_save_srcs ~dests:!callee_save_dests in
      let acc_rev'' = List.rev_append callee_save_instrs acc_rev' in
      translate_block_acc rest acc_rev''
    | Return ret_opnd_op :: instrs ->
      let srcs = !callee_save_dests in
      let dests = !callee_save_srcs in
      let callee_restore_instrs = List.rev_append (mov_args ~srcs ~dests) acc_rev in
      let acc_rev' =
        (* TODO: The argument of the Return constructor is no longer needed here, and there should
           probably be a separate language for after convention translation that doesn't have it.
           Other things that are now unnecessary are the param_temp fields in function labels. *)
        (match ret_opnd_op with
        | Some ret_opnd ->
          let rax = STIR.(Reg { reg = AS.RAX ; size = size_of ret_opnd }) in
          QWT.Return (Some rax) :: QWT.Mov { src = ret_opnd ; dest = rax } :: callee_restore_instrs
        | None ->
          QWT.Return None :: callee_restore_instrs )
      in
      translate_block_acc instrs acc_rev'
    | (Call c as instr) :: instrs ->
      let srcs = temps_to_operands c.fn_label.param_temps in
      let dests =
        gen_args c.fn_label.param_temps
          ~int_size_to_stack_arg:(fun i s -> STIR.Arg_Out_Stack_Idx { idx = i ; size = s})
      in
      let arg_set_instrs = mov_args ~srcs ~dests in
      let acc_rev' = (match c.dest with
        | Some dest ->       
          let rax = STIR.(Reg { reg = AS.RAX ; size = dest.size }) in
          QWT.Mov { src = rax ; dest = STIR.Temp dest }
          :: instr
          :: List.rev_append arg_set_instrs acc_rev
        | None -> 
          instr :: List.rev_append arg_set_instrs acc_rev)
      in
      translate_block_acc instrs acc_rev'
    | QWT.Mem_read load :: instrs ->
      let rax = STIR.(Reg { reg = AS.RAX ; size = STIR.size_of load.dest }) in
      let acc_rev' =
        QWT.Mov { src = rax ; dest = load.dest }
        :: QWT.Mem_read { load with dest = rax }
        :: acc_rev
      in
      translate_block_acc instrs acc_rev'
    | (QWT.Unop uop) as instr :: instrs ->
      (match uop.op with
      | AS.LEA ->
        let rax = STIR.(Reg { reg = AS.RAX ; size = STIR.size_of uop.dest }) in
        let acc_rev' =
          QWT.Mov { src = rax ; dest = uop.dest }
          :: QWT.Unop { uop with dest = rax }
          :: acc_rev
        in
        translate_block_acc instrs acc_rev'
      | _ -> translate_block_acc instrs (instr :: acc_rev))
    | QWT.Mem_write store :: instrs ->
      let rax = STIR.(Reg { reg = AS.RAX ; size = STIR.size_of store.src }) in
      let acc_rev' =
        QWT.Mem_write { store with src = rax }
        :: QWT.Mov { src = store.src ; dest = rax}
        :: acc_rev
      in
      translate_block_acc instrs acc_rev'
    | instr :: instrs -> translate_block_acc instrs (instr :: acc_rev)
  in
  let translate_block (label : CFG.label) : unit =
    let block' = translate_block_acc (CFG.get_data_exn cfg ~label) [] |> List.rev in
    CFG.set_data cfg ~label ~data:block'
  in
  CFG.reverse_postorder_forward cfg |> List.iter ~f:translate_block ;
  cfg

(* TODO: fix these later maybe *)
(* ---------------------------------------- EXPECT TESTS  ----------------------------------------*)
(* module AST = Ast
module IR = Ir_trans
module Q_Trans = Three_addr_trans

let gen_masn ~sym ~exp = AST.Assign { sym ; exp } |> Mark.naked
let gen_mret exp = AST.Return exp |> Mark.naked
let gen_mconst c = Int32.of_int_exn c |> AST.Const |> Mark.naked
let gen_mvar v = AST.Var v |> Mark.naked
let gen_mfdefn ?t ~n ~ps ~b =
  AST.Fdefn { ret_type = t ; ident = n ; param_list = ps ; block = b } |> Mark.naked
let%expect_test
  "Test calling convention translation of a program that calls a function foo from main." =
  Temp.reset ();
  let foo_name = Symbol.symbol "foo" in 
  let var_c = Symbol.symbol "c" |> gen_mvar in
  let sym_x = Symbol.symbol "x" in
  let asn_exp =
    AST.(Pure { lhs = var_c ; rhs = gen_mconst 10 ; op = Plus })
    |> Mark.naked in
  let asn_and_ret = 
    AST.Block [ gen_masn ~sym:sym_x ~exp:asn_exp
              ; Some (gen_mvar sym_x) |> gen_mret ]
    |> Mark.naked
  in
  let decl_x = AST.(Declare { typ = Int ; sym = sym_x ; mstm = asn_and_ret }) |> Mark.naked in

  let main_name = Symbol.symbol "main" in
  let call_args =
    String.split ~on:' ' "1 2 3 4 5 6 7 8 9"
    |> List.map ~f:Int.of_string
    |> List.map ~f:gen_mconst in
  let call = AST.Fn_Call { ident = foo_name ; arg_list = call_args } |> Mark.naked in
  let call_and_ret = AST.Block [ Some call |> gen_mret ] |> Mark.naked in

  let param_names = String.split ~on:' ' "a b c d e f g h i" |> List.map ~f:Symbol.symbol in
  let param_types = String.split ~on:' ' "a b c d e f g h i" |> List.map ~f:(fun _ -> AST.Int) in
  let param_list : AST.param list = 
    List.zip_exn param_names param_types
    |> List.map ~f:(fun (ident, type_) -> AST.{ type_ ; ident })
  in
  let ast_program = 
    AST.[ gen_mfdefn ~t:Int ~n:foo_name ~ps:param_list ~b:[decl_x]
        ; gen_mfdefn ~t:Int ~n:main_name ~ps:[] ~b:[call_and_ret] ]
  in
  let gdecl_ctxts = Typechecker.typecheck ast_program in
  let ir_program = IR.translate ast_program gdecl_ctxts in
  let qwt_program = Q_Trans.codegen ir_program in 
  let qwt_program_conv = translate qwt_program in
  prerr_endline (Print_utils.pp_list ~f:QWT.format ~sep:"\n" qwt_program_conv);
  [%expect
    {|
    _c0_foo(%t1, %t2, %t3, %t4, %t5, %t6, %t7, %t8, %t9):
    	%t1 <-- %EDI
    	%t2 <-- %ESI
    	%t3 <-- %EDX
    	%t4 <-- %ECX
    	%t5 <-- %R8D
    	%t6 <-- %R9D
    	%t7 <-- %arg_in_6
    	%t8 <-- %arg_in_7
    	%t9 <-- %arg_in_8
    	%t23 <-- %EBX
    	%t24 <-- %R12D
    	%t25 <-- %R13D
    	%t26 <-- %R14D
    	%t27 <-- %R15D
    	%t12 <-- %t3
    	%t13 <-- $10
    	%t10 <-- %t12 + %t13
    	%EAX <-- %t10
    	%EBX <-- %t23
    	%R12D <-- %t24
    	%R13D <-- %t25
    	%R14D <-- %t26
    	%R15D <-- %t27
    	ret
    _c0_main():
    	%t28 <-- %EBX
    	%t29 <-- %R12D
    	%t30 <-- %R13D
    	%t31 <-- %R14D
    	%t32 <-- %R15D
    	%t14 <-- $1
    	%t15 <-- $2
    	%t16 <-- $3
    	%t17 <-- $4
    	%t18 <-- $5
    	%t19 <-- $6
    	%t20 <-- $7
    	%t21 <-- $8
    	%t22 <-- $9
    	%EDI <-- %t14
    	%ESI <-- %t15
    	%EDX <-- %t16
    	%ECX <-- %t17
    	%R8D <-- %t18
    	%R9D <-- %t19
    	%arg_out_6 <-- %t20
    	%arg_out_7 <-- %t21
    	%arg_out_8 <-- %t22
    	call _c0_foo(%t14, %t15, %t16, %t17, %t18, %t19, %t20, %t21, %t22)
    	%t11 <-- %EAX
    	%EAX <-- %t11
    	%EBX <-- %t28
    	%R12D <-- %t29
    	%R13D <-- %t30
    	%R14D <-- %t31
    	%R15D <-- %t32
    	ret
  |}]
;; *)
