(* Implements translation from a quad abstract assembly with infinite temp registers to an
 * equivalent representation using a limited number of registers, utilizing stack spillover
 * positions as necessary.
 * 
 * The purpose of this tree translation is to simplify casing when generating x64 assembly, so that 
 * the x64 generation does not have to worry about converting temps to registers using the mapping 
 * generated by the register allocator
 *)
open Core

module AS = Assem
module AL = Assem.Label
module R = Regalloc
module QWT = AS.Quad_With_Temps
module QR = AS.Quad_Regalloc
module STIR = AS.Stack_Temp_Imm_Reg
module SIR = AS.Stack_Imm_Reg

let sir_rsp = SIR.reg_to_op_64 AS.RSP

let generate_fn_to_max_args (program : QWT.instr list) : int Symbol.Map.t = 
  let aggregate_set (s, cur_fn_opt) instr =
    match instr with
    | QWT.Label (AL.Fn_label f) -> (Symbol.Map.add_exn s ~key:f.name ~data:0, Some f.name)
    | QWT.Call c ->
      let cur_fn = Option.value_exn cur_fn_opt in
      let num_params = List.length c.fn_label.param_temps in
      let max_params =  Symbol.Map.find_exn s cur_fn |> Int.max num_params in
      (Symbol.Map.set s ~key:cur_fn ~data:max_params, cur_fn_opt)
    | _ -> (s, cur_fn_opt)
  in
  let (result, _) = List.fold program ~f:aggregate_set ~init:(Symbol.Map.empty, None) in
  result

let translate_to_quad_regalloc ?(coalesce = false) ?(regalloc_cfg = false) qwt_instr_list qwt_cfg = 
  (* Generates register allocation mapping *)
  let (temp_to_reg, fn_to_spill_count) =
    if regalloc_cfg then
      R.generate_mapping_cfg qwt_cfg ~coalesce
    else
      R.generate_mapping qwt_instr_list ~coalesce
  in
  let fn_to_max_args_m = generate_fn_to_max_args qwt_instr_list in
  let rec translate_tail_rec 
          (prog : QWT.instr list)
          (prev_fn : AL.fn_label)
          (acc : QR.instr list) : QR.instr list =
    let cur_fn = match prog with | QWT.Label (AL.Fn_label f) :: _ -> f | _ -> prev_fn in
    let max_args = Symbol.Map.find_exn fn_to_max_args_m cur_fn.name in
    let max_stack_args = List.length AS.x86_arg_regs |> Int.(-) max_args |> Int.max 0 in
    let spill_count = Symbol.Map.find_exn fn_to_spill_count cur_fn.name in
    let total_used_slots = max_stack_args + spill_count in
    (* The frame size should 8 mod 16 aligned because after pushing the return address, the stack is
      8 mod 16. *)
    let num_frame_slots = total_used_slots + (total_used_slots % 2 + 1) in
    let frame_size = num_frame_slots * AS.word_size in
    let rti_to_rsti = function
      | STIR.Reg _ | STIR.Temp _ as x ->
        (match temp_to_reg x with
        | SIR.Stack_Offset i ->
          SIR.Stack_Offset { i with idx = i.idx + (AS.word_size * max_stack_args) }
        | reg -> reg)
      | STIR.Arg_In_Stack_Idx i ->
        (* Adding the frame size to RSP yields the return address, so 1 above that lies the stack
           args *)
        SIR.Stack_Offset { i with idx = (AS.word_size * (i.idx + num_frame_slots + 1)) }
      | STIR.Arg_Out_Stack_Idx i ->
        SIR.Stack_Offset { i with idx = (AS.word_size * i.idx) }
      | STIR.Imm32 x -> SIR.Imm32 x
      | STIR.Imm64 x -> SIR.Imm64 x
      | STIR.Addr_mode exp ->
        let disp = exp.disp in
        let base = STIR.Temp exp.base |> temp_to_reg in
        let index = STIR.Temp exp.index |> temp_to_reg in
        let scale = exp.scale in
        SIR.Addr_mode { disp ; base ; index ; scale }
    in
    match prog with
    | [] -> acc
    | line :: lines -> 
      let acc' =
        match line with
        | QWT.Binop b -> 
          QR.Binop { op = b.op ; dest = rti_to_rsti b.dest
                   ; lhs = rti_to_rsti b.lhs ; rhs = rti_to_rsti b.rhs } :: acc
        | QWT.Unop u ->
          QR.Unop { op = u.op ; dest = rti_to_rsti u.dest ; src = rti_to_rsti u.src } :: acc
        | QWT.Mov m -> 
          QR.Mov { dest = rti_to_rsti m.dest ; src = rti_to_rsti m.src } :: acc
        | QWT.If i -> 
          QR.If { op = i.op ; lhs = rti_to_rsti i.lhs ; rhs = rti_to_rsti i.rhs
                ; if_true = i.if_true ; if_false = i.if_false } :: acc
        | QWT.Goto l -> (QR.Goto l) :: acc
        | QWT.Call c -> (QR.Call c) :: acc
        | QWT.Label ((AL.Fn_label _) as lbl) -> 
          QR.Binop
            { op = AS.Sub ; dest = sir_rsp ; lhs = sir_rsp
            ; rhs = SIR.Imm64 (Int64.of_int_exn frame_size) }
          :: (QR.Label lbl)
          :: acc
        | QWT.Label l -> (QR.Label l) :: acc
        | QWT.Return op_opt -> 
          QR.Return (Option.map ~f:rti_to_rsti op_opt)
          :: QR.Binop
            { op = AS.Add ; dest = sir_rsp ; lhs = sir_rsp
            ; rhs = SIR.Imm64 (Int64.of_int_exn frame_size) }
          :: acc 
        | QWT.Mem_read r -> (QR.Mem_read { dest = rti_to_rsti r.dest ; src = rti_to_rsti r.src }) :: acc
        | QWT.Mem_write r -> (QR.Mem_write { dest = rti_to_rsti r.dest ; src = rti_to_rsti r.src }) :: acc
        | QWT.Directive d -> (QR.Directive d) :: acc
        | QWT.Comment _ -> acc
        | QWT.Phi _ -> failwith "Phi function should not be in register allocated code"
      in
      translate_tail_rec lines cur_fn acc'
  in
  match qwt_instr_list with
  | QWT.Label (AL.Fn_label f) :: _ -> translate_tail_rec qwt_instr_list f [] |> List.rev
  | _ -> 
    sprintf "Malformed program:\n%s" (Print_utils.pp_list qwt_instr_list ~sep:"\n" ~f:QWT.format)
    |> failwith
  
;;

(* TODO: fix expect tests maybe perhaps potentially later *)
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
  "Test operand translation of a program that calls a function foo from main." =
  Temp.reset ();
  let foo_name = Symbol.symbol "foo" in 
  let var_c = Symbol.symbol "c" |> gen_mvar in
  let sym_x = Symbol.symbol "x" in
  let asn_exp =
    AST.(Pure { lhs = var_c ; rhs = gen_mconst 10 ; op = Plus })
    |> Mark.naked in
  let asn_and_ret = 
    AST.Block [ gen_masn ~sym:sym_x ~exp:asn_exp ; Some (gen_mvar sym_x) |> gen_mret ] |> Mark.naked
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
  let qwt_program_conv = Convention_trans.translate qwt_program in
  let (qr_program, _) = translate_to_quad_regalloc qwt_program_conv in
  prerr_endline (Print_utils.pp_list ~f:QR.format ~sep:"\n" qr_program);
  [%expect
    {|
    _c0_foo(%t1, %t2, %t3, %t4, %t5, %t6, %t7, %t8, %t9):
    	PUSHQ %RBP
    	SUBQ $0, %RSP
    	%EDI <-- %EDI
    	%ESI <-- %ESI
    	%ESI <-- %EDX
    	%EDI <-- %ECX
    	%R8D <-- %R8D
    	%R8D <-- %R9D
    	%R8D <-- 16(%rsp)
    	%R8D <-- 24(%rsp)
    	%R8D <-- 32(%rsp)
    	%EDI <-- %EBX
    	%R12D <-- %R12D
    	%R11D <-- %R13D
    	%R10D <-- %R14D
    	%R8D <-- %R15D
    	%ESI <-- %ESI
    	%R13D <-- $10
    	%ESI <-- %ESI + %R13D
    	%EAX <-- %ESI
    	%EBX <-- %EDI
    	%R12D <-- %R12D
    	%R13D <-- %R11D
    	%R14D <-- %R10D
    	%R15D <-- %R8D
    	ADDQ $0, %RSP
    	POPQ %RBP
    	ret
    _c0_main():
    	PUSHQ %RBP
    	SUBQ $32, %RSP
    	%EBX <-- %EBX
    	%R12D <-- %R12D
    	%R13D <-- %R13D
    	%R14D <-- %R14D
    	%EBP <-- %R15D
    	%EDI <-- $1
    	%ESI <-- $2
    	%EDX <-- $3
    	%ECX <-- $4
    	%R8D <-- $5
    	%R9D <-- $6
    	%R10D <-- $7
    	%R11D <-- $8
    	%EAX <-- $9
    	%EDI <-- %EDI
    	%ESI <-- %ESI
    	%EDX <-- %EDX
    	%ECX <-- %ECX
    	%R8D <-- %R8D
    	%R9D <-- %R9D
    	0(%rsp) <-- %R10D
    	8(%rsp) <-- %R11D
    	16(%rsp) <-- %EAX
    	call _c0_foo(%t14, %t15, %t16, %t17, %t18, %t19, %t20, %t21, %t22)
    	%ESI <-- %EAX
    	%EAX <-- %ESI
    	%EBX <-- %EBX
    	%R12D <-- %R12D
    	%R13D <-- %R13D
    	%R14D <-- %R14D
    	%R15D <-- %EBP
    	ADDQ $32, %RSP
    	POPQ %RBP
    	ret
  |}]
;;

let%expect_test
  "Test operand translation of a program that calls a function foo from main with coalescing." =
  Temp.reset ();
  let foo_name = Symbol.symbol "foo" in 
  let var_c = Symbol.symbol "c" |> gen_mvar in
  let sym_x = Symbol.symbol "x" in
  let asn_exp =
    AST.(Pure { lhs = var_c ; rhs = gen_mconst 10 ; op = Plus })
    |> Mark.naked in
  let asn_and_ret = 
    AST.Block [ gen_masn ~sym:sym_x ~exp:asn_exp ; Some (gen_mvar sym_x) |> gen_mret ] |> Mark.naked
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
  let qwt_program_conv = Convention_trans.translate qwt_program in
  let (qr_program, _) = translate_to_quad_regalloc qwt_program_conv ~coalesce:true in
  prerr_endline (Print_utils.pp_list ~f:QR.format ~sep:"\n" qr_program);
  [%expect
    {|
    _c0_foo(%t1, %t2, %t3, %t4, %t5, %t6, %t7, %t8, %t9):
    	PUSHQ %RBP
    	SUBQ $0, %RSP
    	%EDI <-- %EDI
    	%ESI <-- %ESI
    	%EDX <-- %EDX
    	%ECX <-- %ECX
    	%R8D <-- %R8D
    	%R9D <-- %R9D
    	%ESI <-- 16(%rsp)
    	%ESI <-- 24(%rsp)
    	%ESI <-- 32(%rsp)
    	%EBX <-- %EBX
    	%R12D <-- %R12D
    	%R13D <-- %R13D
    	%R14D <-- %R14D
    	%ESI <-- %R15D
    	%EDX <-- %EDX
    	%R8D <-- $10
    	%EAX <-- %EDX + %R8D
    	%EAX <-- %EAX
    	%EBX <-- %EBX
    	%R12D <-- %R12D
    	%R13D <-- %R13D
    	%R14D <-- %R14D
    	%R15D <-- %ESI
    	ADDQ $0, %RSP
    	POPQ %RBP
    	ret
    _c0_main():
    	PUSHQ %RBP
    	SUBQ $32, %RSP
    	%EBX <-- %EBX
    	%R12D <-- %R12D
    	%R13D <-- %R13D
    	%R14D <-- %R14D
    	%EBP <-- %R15D
    	%EDI <-- $1
    	%ESI <-- $2
    	%EDX <-- $3
    	%ECX <-- $4
    	%R8D <-- $5
    	%R9D <-- $6
    	%R10D <-- $7
    	%R11D <-- $8
    	%EAX <-- $9
    	%EDI <-- %EDI
    	%ESI <-- %ESI
    	%EDX <-- %EDX
    	%ECX <-- %ECX
    	%R8D <-- %R8D
    	%R9D <-- %R9D
    	0(%rsp) <-- %R10D
    	8(%rsp) <-- %R11D
    	16(%rsp) <-- %EAX
    	call _c0_foo(%t14, %t15, %t16, %t17, %t18, %t19, %t20, %t21, %t22)
    	%EAX <-- %EAX
    	%EAX <-- %EAX
    	%EBX <-- %EBX
    	%R12D <-- %R12D
    	%R13D <-- %R13D
    	%R14D <-- %R14D
    	%R15D <-- %EBP
    	ADDQ $32, %RSP
    	POPQ %RBP
    	ret
  |}]
;; *)