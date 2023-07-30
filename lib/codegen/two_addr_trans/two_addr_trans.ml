(* L4 Compiler
 * Generate x86_64 from 3-addr abstract assembly
 *)

open Core

module A = Assem
module AL = A.Label
open A.X86_Assem
module QR = A.Quad_Regalloc
module SIR = A.Stack_Imm_Reg

let stack_reg = A.stack_reserve_reg
let stack_reg_32 = A.stack_reserve_reg_32
let stack_reg_64 = A.stack_reserve_reg_64

let mem_reg_64 = A.mem_reserve_reg_64

let mem_reg = A.mem_reserve_reg

let q2_to_tr2 = function
| A.Add -> ADD
| A.Sub -> SUB
| A.Mul -> IMUL
| A.LShift -> SAL
| A.RShift -> SAR
| A.RShift_unsigned -> SHR
| A.BWXor -> XOR
| A.BWAnd -> AND
| A.BWOr -> OR
| A.Mod | A.Div -> failwith "Division and modulo are not two-operand operators in x86 assembly "

let q2_to_trjmp = function
| A.LessThan -> JL
| A.LessThanEq -> JLE 
| A.GreaterThan -> JG 
| A.GreaterThanEq -> JGE
| A.EqualsTo -> JE
| A.NotEqualsTo -> JNE

(* Flip way the comparison operator would if both sides were multiplied by -1 *)
let flip_jmp = function
  | JL -> JG
  | JLE -> JGE
  | JG -> JL
  | JGE -> JLE
  | JE -> JE
  | JNE -> JNE
  | JMP -> JMP

let exception_block (int_label : AL.t) (acc : x86_instr list) =
  Call (Symbol.symbol "raise") 
  :: TwoOp
    { op = MOV
    ; src = AL.lbl_to_int int_label |> Int32.of_int_exn |> SIR.Imm32
    ; dest = Reg { size = A.S_32 ; reg = A.RDI } }
  :: Local_label (AL.format_label int_label |> Symbol.symbol)
  :: acc

let fill_addressing_mode_regs (addr_mode : SIR.t) (acc : program) : program * SIR.t =
  let fill_reg_if_stack ~reg ~src acc =
    (match src with
    | SIR.Reg _ -> (acc, src)
    | SIR.Stack_Offset _ ->
      (TwoOp { op = MOV ; src ; dest = reg } :: acc, reg)
    | _ -> failwith "Expected addressing mode argument to be a register or stack location")
  in
  match addr_mode with
  | SIR.Addr_mode exp ->
    (match (exp.base, exp.index) with
    | (SIR.Reg _, SIR.Reg _) -> (acc, addr_mode)
    | (SIR.Imm32 _, _) | (SIR.Imm64 _, _) | (_, SIR.Imm32 _) | (_, SIR.Imm64 _) ->
      failwith "Base and index of addressing mode cannot be immediates"
    | _ ->
      let (acc', base') = fill_reg_if_stack ~reg:(SIR.Reg stack_reg_64) ~src:(exp.base) acc in
      let (acc'', index') = fill_reg_if_stack ~reg:(SIR.Reg mem_reg_64) ~src:(exp.index) acc' in
      (acc'', SIR.Addr_mode { exp with base = base' ; index = index' }))
  | _ -> failwith "Expected an addressing mode"

(* Function that generates x86_64 assembly *)
let x86_gen instr_list =
  (* Function that generates all lines, takes in QR.instr list and accumulated x86_instr list *)
  let rec gen_lines (instr_list : QR.instr list) (acc_instrs : x86_instr list) = 
    match instr_list with
    | [] -> acc_instrs
    | line :: lines -> 
      match line with
      | QR.Binop b ->
        let dest_reg : A.sized_reg = match b.dest with 
          | SIR.Stack_Offset s -> { reg = stack_reg ; size = s.size }
          | SIR.Reg r -> r 
          | SIR.Addr_mode _ -> failwith "A binop destination cannot be a non-stack addressing mode"
          | SIR.Imm32 _ | SIR.Imm64 _ -> failwith "A binop destination cannot be an immediate" 
        in
        let dest_op = SIR.Reg dest_reg in
        let acc_instrs' = match b.op with
          | A.Add | A.BWAnd | A.BWXor | A.BWOr -> gen_binop_comm line dest_op dest_reg acc_instrs
          | A.Sub | A.LShift | A.RShift | A.RShift_unsigned ->
            gen_binop_not_comm line dest_op dest_reg acc_instrs
          | A.Mul -> gen_binop_comm line dest_op dest_reg acc_instrs
          | A.Div | A.Mod ->
            let (rhs, acc') =
              (match b.rhs with
              | SIR.Imm32 _->
                (SIR.Reg stack_reg_32,
                (TwoOp { op = MOV ; src = b.rhs ; dest = SIR.Reg stack_reg_32 }) :: acc_instrs)
              | SIR.Imm64 _ ->
                (SIR.Reg stack_reg_64,
                (TwoOp { op = MOV ; src = b.rhs ; dest = SIR.Reg stack_reg_64 }) :: acc_instrs)
              | SIR.Stack_Offset _ | SIR.Reg _ -> (b.rhs, acc_instrs)
              | SIR.Addr_mode _ -> failwith "div/mod operands cannot be non-stack address modes")
            in
              (OneOp { op = IDIV ; operand = rhs }) :: acc'
        in
        gen_lines lines acc_instrs'
      | QR.Unop u ->
        let acc_instrs' = (match u.op with 
          | A.CDQ -> (ZeroOp CDQ) :: acc_instrs
          | A.MOVSXD ->
            (match u.dest with
            | SIR.Stack_Offset _ -> 
              (TwoOp { op = MOV ; src = SIR.Reg { size = A.S_64 ; reg = stack_reg } ; dest = u.dest })
              :: (TwoOp { op = MOVSXD ; src = u.src ; dest = SIR.Reg { size = A.S_64 ; reg = stack_reg }})
              :: acc_instrs
            | _ -> (TwoOp { op = MOVSXD ; src = u.src ; dest = u.dest }) :: acc_instrs)
          | A.LEA -> 
            let (acc', filled_addr_mode) = fill_addressing_mode_regs u.src acc_instrs in
            TwoOp { op = LEA ; src = filled_addr_mode ; dest = u.dest } :: acc')
        in 
        gen_lines lines acc_instrs'
      | QR.Mov _ -> gen_mov line acc_instrs |> gen_lines lines
      | QR.If _ -> gen_if line acc_instrs |> gen_lines lines
      | QR.Goto l ->
        gen_lines lines
          ((JmpOp { op = JMP ; label = AL.format_label l ~fn_args:false |> Symbol.symbol })
        :: acc_instrs)
      | QR.Label (AL.Local_label lbl) ->
        gen_lines lines ((Local_label.name lbl |> Symbol.symbol |> Local_label) :: acc_instrs)
      | QR.Label (AL.Fn_label f) -> gen_lines lines ((Fn_label f.name) :: acc_instrs)
      | QR.Label ((AL.ARITH_LABEL | AL.MEM_LABEL | AL.ENTRY_LABEL | AL.EXIT_LABEL) as lbl) ->
        sprintf "Two address translation does not support top-level three-address label: `%s`" 
          (AL.format_label lbl)
        |> failwith
      | QR.Call c -> gen_lines lines ((Call c.fn_label.name) :: acc_instrs)
      | QR.Return _ -> gen_lines lines (Return :: acc_instrs)
      | QR.Mem_read m -> 
        let (acc0, r_src) =
          (match m.src with
          | SIR.Reg _ -> (acc_instrs, m.src) 
          (* This should always be an address, and size 64 *)
          | SIR.Stack_Offset _ -> 
            let mem_src : SIR.t = SIR.Reg { reg = mem_reg ; size = A.S_64 } in
            ((TwoOp { op = MOV ; src = m.src ; dest = mem_src } ) :: acc_instrs, mem_src) 
          | SIR.Addr_mode _ -> fill_addressing_mode_regs m.src acc_instrs
          | SIR.Imm32 _ | SIR.Imm64 _ -> failwith "Immediate cannot be pointer address") in
        let acc1 = (match m.dest with 
          | SIR.Reg r -> (Mem_read { src = r_src ; dest = r }) :: acc0
          | SIR.Stack_Offset s -> 
            let r_dest : A.sized_reg = { reg = stack_reg ; size = s.size } in
            (TwoOp { op = MOV ; src = SIR.Reg r_dest ; dest = m.dest }) 
            :: (Mem_read { src = r_src ; dest = r_dest }) :: acc0
          | SIR.Addr_mode _ -> failwith "Address mode expression cannot be dest of mem read"
          | SIR.Imm32 _ | SIR.Imm64 _ -> failwith "immediate cannot be destination") in
        gen_lines lines acc1
      | QR.Mem_write m -> 
        let (acc0, r_src) =
          (match m.src with
          | SIR.Reg _ | SIR.Imm32 _ | SIR.Imm64 _ -> (acc_instrs,m.src)
          | SIR.Stack_Offset s -> 
            let mem_src = SIR.Reg { reg = stack_reg ; size = s.size } in 
            ((TwoOp { op = MOV ; src = m.src ; dest = mem_src } ) :: acc_instrs, mem_src)
          | SIR.Addr_mode _ -> failwith "Source of mem write cannot be a non-stack address mode")
        in
        let acc1 = (match m.dest with 
          | SIR.Reg _ -> (Mem_write { src = r_src ; dest = m.dest }) :: acc0
          | SIR.Stack_Offset s ->
            let r_dest : SIR.t = SIR.Reg { reg = mem_reg ; size = s.size} in
            (Mem_write { src = r_src ; dest = r_dest } )
            :: (TwoOp { op = MOV ; src = m.dest ; dest = r_dest}) :: acc0
          | SIR.Addr_mode _ ->
            let (acc', filled_addr_mode) = fill_addressing_mode_regs m.dest acc0 in
            (Mem_write { src = r_src ; dest = filled_addr_mode }) :: acc'
          | SIR.Imm32 _ | SIR.Imm64 _ -> failwith "immediate cannot be pointer address") in
        gen_lines lines acc1
      | QR.Directive d -> gen_lines lines (Directive d :: acc_instrs)
      | QR.Comment _ -> gen_lines lines acc_instrs
      | QR.Phi _ -> failwith "Phi functions should never be in two addr trans"

  (* Note: Works for 64 bit immediates *)
  and gen_binop_comm binop dest_op dest_reg acc_instrs = match binop with
    | QR.Binop b ->
      let is_64 opnd = (match opnd with 
        | SIR.Imm64 c ->
          if (Int64.(>) c (Int64.of_int32 (Int32.max_value))) || (Int64.(<) c Int64.zero) then 
            true 
          else 
            false
        | _ -> false) in
      let st_reg_64 = SIR.Reg { reg = stack_reg ; size = A.S_64 } in
      let bop = q2_to_tr2 b.op in 
      let lhs_is_64 = is_64 b.lhs in
      let rhs_is_64 = is_64 b.rhs in
      let acc_instrs' = 
      
        if (SIR.equal b.lhs dest_op) then 
          if rhs_is_64 then
            ((TwoOp { op = bop ; src = st_reg_64 ; dest = dest_op })
            :: (TwoOp { op = MOV ; src = b.rhs ; dest = st_reg_64 }) :: acc_instrs)
          else
            ((TwoOp { op = bop ; src = b.rhs ; dest = dest_op }) :: acc_instrs)
        else if (SIR.equal b.rhs dest_op) then 
          if lhs_is_64 then
            ((TwoOp { op = bop ; src = st_reg_64 ; dest = dest_op })
            :: (TwoOp { op = MOV ; src = b.lhs ; dest = st_reg_64 }) :: acc_instrs)
          else
            ((TwoOp { op = bop ; src = b.lhs ; dest = dest_op }) :: acc_instrs)
        else 
          if lhs_is_64 then
            ((TwoOp { op = bop ; src = b.rhs ; dest = dest_op })
            :: (TwoOp { op = MOV ; src = b.lhs ; dest = dest_op }) :: acc_instrs)
          else if rhs_is_64 then
            ((TwoOp { op = bop ; src = b.lhs ; dest = dest_op })
            :: (TwoOp { op = MOV ; src = b.rhs ; dest = dest_op }) :: acc_instrs)
          else
            ((TwoOp { op = bop ; src = b.rhs ; dest = dest_op })
            :: (TwoOp { op = MOV ; src = b.lhs ; dest = dest_op }) :: acc_instrs)
      in
      if (A.equal_x86_reg_64 dest_reg.reg stack_reg) then
        (TwoOp { op = MOV ; src = dest_op ; dest = b.dest }) :: acc_instrs'
      else acc_instrs'
    | _ -> failwith "Expected a binop"

  (* Note: Does not work for 64 bit immediates *)
  and gen_binop_not_comm binop dest_op dest_reg acc_instrs = match binop with
    | QR.Binop b ->
      let bop = q2_to_tr2 b.op in
      let acc_instrs' = 
        if (SIR.equal b.lhs dest_op) then 
          ((TwoOp { op = bop ; src = b.rhs ; dest = dest_op }) :: acc_instrs)
        else 
          (if (SIR.equal b.rhs dest_op) then 
            let placeholder_dest = 
              (match b.rhs with
              | SIR.Imm32 _ -> stack_reg_32
              | SIR.Imm64 _ -> stack_reg_64
              | SIR.Reg r -> (match r.size with A.S_32 -> stack_reg_32 | A.S_64 -> stack_reg_64)
              | SIR.Stack_Offset _ -> failwith "Destination cannot be stack position"
              | SIR.Addr_mode _ -> failwith "Destination of a binop cannot be an addressing mode ")
              |> SIR.Reg
            in
            (* Works bc dest_op is guaranteed not r15 since b.rhs can't be r15 *)
            (TwoOp { op = MOV ; src = placeholder_dest ; dest = dest_op })
            :: (TwoOp { op = bop ; src = b.rhs ; dest = placeholder_dest })
            :: (TwoOp { op = MOV ; src = b.lhs ; dest = placeholder_dest  }) 
            :: acc_instrs
          else 
            (TwoOp { op = bop ; src = b.rhs ; dest = dest_op })
            :: (TwoOp { op = MOV ; src = b.lhs ; dest = dest_op }) :: acc_instrs)
      in 
      if (A.equal_x86_reg_64 dest_reg.reg stack_reg) then
        (TwoOp { op = MOV ; src = dest_op ; dest = b.dest }) :: acc_instrs'
      else acc_instrs' 
    | _ -> failwith "Expected a binop"

  and gen_mov mov acc_instrs = match mov with
    | QR.Mov m -> (match (m.src, m.dest) with 
      | (Reg _,_) |  (Imm32 _, _) | (Imm64 _, _) | (_, Reg _) ->
        (TwoOp { op = MOV; src = m.src ; dest = m.dest }) :: acc_instrs
      | _ -> 
        (TwoOp
          { op = MOV ; src = SIR.Reg { reg = stack_reg ; size = SIR.operand_size m.src }
          ; dest = m.dest })
        :: (TwoOp
          { op = MOV ; src = m.src
          ; dest = SIR.Reg { reg = stack_reg ; size = SIR.operand_size m.src } }) 
        :: acc_instrs)
    | _ -> failwith "Expected a mov"

  and gen_if if_stm acc_instrs = match if_stm with
    | QR.If i -> 
      let (cop, cmp_acc) =
        (match (i.lhs, i.rhs) with
          | (SIR.Stack_Offset _, SIR.Stack_Offset _) -> 
            let cop = q2_to_trjmp i.op in
            let dest = SIR.Reg { reg = stack_reg ; size = SIR.operand_size i.rhs } in
            let acc' =
              (TwoOp { op = CMP ; src = i.rhs ; dest })
              :: (TwoOp { op = MOV ; src = i.lhs ; dest }) 
              :: acc_instrs
            in
            (cop, acc')
          | (SIR.Imm32 _, _) | (SIR.Imm64 _, _) ->
            let cop = q2_to_trjmp i.op |> flip_jmp in
            let acc' = (TwoOp { op = CMP ; src = i.lhs ; dest = i.rhs }) :: acc_instrs in
            (cop, acc')
          | _ ->
            let cop = q2_to_trjmp i.op in
            let acc' = (TwoOp { op = CMP ; src = i.rhs ; dest = i.lhs }) :: acc_instrs in
            (cop, acc'))
      in 
      let label_no_args = Fn.compose Symbol.symbol (AL.format_label ~fn_args:false) in
      (JmpOp { op = JMP ; label = label_no_args i.if_false })
      :: (JmpOp { op = cop ; label = label_no_args i.if_true }) :: cmp_acc
    | _ -> failwith "Expected an if" 
  in
  let rev_instrs =
    gen_lines instr_list [] |> exception_block AL.MEM_LABEL |> exception_block AL.ARITH_LABEL
  in
  List.rev rev_instrs

(* Fix these maybe possibly eventually *)
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
  let sym_x = Symbol.symbol "j" in
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
  let (qr_program, i) = Reg_trans.translate_to_quad_regalloc qwt_program_conv in
  let x86_program = x86_gen qr_program i in
  prerr_endline (Print_utils.pp_list ~f:format ~sep:"\n" x86_program);
  [%expect
    {|
    .globl _c0_foo
    _c0_foo:
    	PUSHQ %RBP
    	SUBQ $0, %RSP
    	MOVL %EDI, %EDI
    	MOVL %ESI, %ESI
    	MOVL %EDX, %ESI
    	MOVL %ECX, %EDI
    	MOVL %R8D, %R8D
    	MOVL %R9D, %R8D
    	MOVL 16(%rsp), %R8D
    	MOVL 24(%rsp), %R8D
    	MOVL 32(%rsp), %R8D
    	MOVL %EBX, %EDI
    	MOVL %R12D, %R12D
    	MOVL %R13D, %R11D
    	MOVL %R14D, %R10D
    	MOVL %R15D, %R8D
    	MOVL %ESI, %ESI
    	MOVL $10, %R13D
    	ADD %R13D, %ESI
    	MOVL %ESI, %EAX
    	MOVL %EDI, %EBX
    	MOVL %R12D, %R12D
    	MOVL %R11D, %R13D
    	MOVL %R10D, %R14D
    	MOVL %R8D, %R15D
    	ADDQ $0, %RSP
    	POPQ %RBP
    	RET
    .globl _c0_main
    _c0_main:
    	PUSHQ %RBP
    	SUBQ $32, %RSP
    	MOVL %EBX, %EBX
    	MOVL %R12D, %R12D
    	MOVL %R13D, %R13D
    	MOVL %R14D, %R14D
    	MOVL %R15D, %EBP
    	MOVL $1, %EDI
    	MOVL $2, %ESI
    	MOVL $3, %EDX
    	MOVL $4, %ECX
    	MOVL $5, %R8D
    	MOVL $6, %R9D
    	MOVL $7, %R10D
    	MOVL $8, %R11D
    	MOVL $9, %EAX
    	MOVL %EDI, %EDI
    	MOVL %ESI, %ESI
    	MOVL %EDX, %EDX
    	MOVL %ECX, %ECX
    	MOVL %R8D, %R8D
    	MOVL %R9D, %R9D
    	MOVL %R10D, 0(%rsp)
    	MOVL %R11D, 8(%rsp)
    	MOVL %EAX, 16(%rsp)
    	CALL _c0_foo
    	MOVL %EAX, %ESI
    	MOVL %ESI, %EAX
    	MOVL %EBX, %EBX
    	MOVL %R12D, %R12D
    	MOVL %R13D, %R13D
    	MOVL %R14D, %R14D
    	MOVL %EBP, %R15D
    	ADDQ $32, %RSP
    	POPQ %RBP
    	RET
  |}]
;; *)
