(* L4 Compiler
 * Assembly Code Generator for FAKE assembly
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Use a linear, not quadratic, algorithm.
 *
 * Implements a "convenient munch" algorithm
 * 
 * The purpose of the Quad assembly with temps is to create a three-address assembly that can be 
 *  easily optimized upon and converted to other three-address assembly languages, namely LLVM IR
 *)

open Core
module T = Ir_tree
module A = Assem
module AL = Assem.Label
module QWT = A.Quad_With_Temps
module STIR = A.Stack_Temp_Imm_Reg

let size_I_exp_pure = function
  | T.Const32 _ | T.Binop_pure _ -> A.S_32
  | T.Const64 _ -> A.S_64
  | T.Temp t -> t.size

let mem_err_if_null (temp : STIR.t) (acc : QWT.instr list) = 
  let not_null_lbl = Local_label.create () |> AL.Local_label in
  let acc0 =
    (QWT.If 
      { op = EqualsTo ; lhs = temp ; rhs = STIR.Imm64 Int64.zero
      ; if_true = AL.MEM_LABEL ; if_false = not_null_lbl }) 
    :: acc in
  (QWT.Label not_null_lbl) :: acc0 

let shift_bounds_check (shift_arg : STIR.t) (acc : QWT.instr list) =
    let non_neg_lbl = Local_label.create () |> AL.Local_label in
    let within_bounds_lbl = Local_label.create () |> AL.Local_label in
    QWT.Label within_bounds_lbl
    :: QWT.If 
      { lhs = shift_arg ; op = A.LessThan ; rhs = STIR.Imm32 (Option.value_exn (Int32.of_int 32))
      ; if_true = within_bounds_lbl ; if_false = AL.ARITH_LABEL }
    :: QWT.Label non_neg_lbl
    :: QWT.If
      { lhs = shift_arg ; op = A.GreaterThanEq ; rhs = STIR.Imm32 Int32.zero
      ; if_true = non_neg_lbl ; if_false = AL.ARITH_LABEL }
    :: acc

let munch_binop_pure = function
  | T.Plus -> A.Add
  | T.Minus -> A.Sub
  | T.Times -> A.Mul
  | T.BitwiseAnd -> A.BWAnd
  | T.BitwiseXor -> A.BWXor
  | T.BitwiseOr -> A.BWOr
;;

(* saved for later, but right now we case directly on the impure operations, and don't wind up
   using this *)
let munch_binop_impure = function
  | T.Divided_by -> A.Div
  | T.Modulo -> A.Mod
  | T.LShift -> A.LShift
  | T.RShift -> A.RShift
;;

let munch_binop_comp = function
  | T.LessThan -> A.LessThan
  | T.LessThanEq -> A.LessThanEq
  | T.GreaterThan -> A.GreaterThan
  | T.GreaterThanEq ->A.GreaterThanEq
  | T.EqualsTo -> A.EqualsTo
  | T.NotEqualsTo -> A.NotEqualsTo
;;

let rec munch_exp_pure_acc 
    (dest : STIR.t) (exp : T.exp_pure) (acc : QWT.instr list) : QWT.instr list =
  match exp with
  | T.Const32 n -> QWT.Mov { dest ; src = STIR.Imm32 n } :: acc
  | T.Const64 n -> QWT.Mov { dest ; src = STIR.Imm64 n } :: acc
  | T.Temp t -> QWT.Mov { dest ; src = STIR.Temp t } :: acc
  | T.Binop_pure binop -> munch_binop_pure_acc dest (binop.op, binop.lhs, binop.rhs) acc
  and munch_binop_pure_acc 
      (dest : STIR.t) ((binop, e1, e2) : T.binop_pure * T.exp_pure * T.exp_pure) 
      (acc : QWT.instr list) : QWT.instr list =
    let op = munch_binop_pure binop in
    let t1 = STIR.Temp ({ temp = Temp.create () ; size = A.S_32 }) in
    let t2 = STIR.Temp ({ temp = Temp.create () ; size = A.S_32 }) in
    let rev_acc' = acc |> munch_exp_pure_acc t1 e1 |> munch_exp_pure_acc t2 e2 in
    QWT.Binop { op ; dest ; lhs = t1 ; rhs = t2 } :: rev_acc'

let munch_binop_exp_impure_acc 
    (lhs : T.exp_pure) (op : T.binop_impure) (rhs : T.exp_pure) (dest : STIR.t) 
    (acc : QWT.instr list) (is_unsafe : bool) (is_llvm : bool)
      : QWT.instr list = 
  let t1 = STIR.Temp({ temp = Temp.create () ; size = A.S_32 }) in 
  let t2 = STIR.Temp({ temp = Temp.create () ; size = A.S_32 }) in
  let acc0 = acc |> munch_exp_pure_acc t1 lhs |> munch_exp_pure_acc t2 rhs in 
  let munch_div_mod op =
    if is_unsafe || (not is_llvm) then 
      QWT.Binop { op ; dest ; lhs = t1 ; rhs = t2} :: acc0
    else
      let nonzero_divsor_lbl = AL.Local_label (Local_label.create ()) in
      let neg1_divisor_lbl = AL.Local_label (Local_label.create ()) in
      let safe_lbl = AL.Local_label (Local_label.create ()) in
      QWT.Binop { op ; dest ; lhs = t1 ; rhs = t2}
      :: QWT.Label safe_lbl
      :: QWT.If
        { lhs = t1 ; rhs = STIR.Imm32 Int32.min_value ; op = A.EqualsTo
        ; if_true = AL.ARITH_LABEL ; if_false = safe_lbl
        }
      :: QWT.Label neg1_divisor_lbl
      :: QWT.If
        { lhs = t2 ; rhs = STIR.Imm32 (Int32.of_int_exn (-1)) ; op = A.EqualsTo
        ; if_true = neg1_divisor_lbl ; if_false = safe_lbl
        }
      :: QWT.Label nonzero_divsor_lbl
      :: QWT.If
        { lhs = t2 ; rhs = STIR.Imm32 Int32.zero ; op = A.EqualsTo
        ; if_true = AL.ARITH_LABEL ; if_false = nonzero_divsor_lbl }
      :: acc0
  in
  match op with 
  | T.Divided_by | T.Modulo -> munch_binop_impure op |> munch_div_mod
  | T.LShift -> 
    QWT.Binop 
      {lhs = t1 ; op = A.LShift ; rhs = t2 ; dest = dest}
    :: (if is_unsafe then acc0 else shift_bounds_check t2 acc0)
  | T.RShift -> 
    QWT.Binop 
      { lhs = t1 ; op = A.RShift ; rhs = t2 ; dest = dest }
      :: (if is_unsafe then acc0 else shift_bounds_check t2 acc0)

let munch_binop_exp_comp_acc (cmd : T.command) (acc : QWT.instr list) : QWT.instr list = 
  match cmd with 
  | T.If i -> 
    let t1 = STIR.Temp ({ temp = Temp.create () ; size = size_I_exp_pure i.lhs }) in 
    let t2 = STIR.Temp ({ temp = Temp.create () ; size = size_I_exp_pure i.rhs }) in
    let acc0 = acc |> munch_exp_pure_acc t1 i.lhs |> munch_exp_pure_acc t2 i.rhs in  
    (QWT.If 
      { lhs = t1 ; op = munch_binop_comp i.op ; rhs = t2
      ; if_true = i.tru |> AL.Local_label ; if_false = i.fls |> AL.Local_label })
    :: acc0
  | _ -> failwith "not an if statement"

let munch_fn_call_acc (arg_list : T.exp_pure list) (name : Symbol.t) (dest : A.sized_temp option) 
   (acc : QWT.instr list) : QWT.instr list =
  let param_temps = 
    List.map ~f:(fun p -> ({ temp = Temp.create () ; size = size_I_exp_pure p } : A.sized_temp)) 
      arg_list in
  let fn_label : AL.fn_label = { name ; param_temps ; ret_size_opt = Option.map dest ~f:(fun d -> d.size) } in 
  let temps_exps = List.zip_exn param_temps arg_list in
  let munch_into_temps acc (t, e) = munch_exp_pure_acc (STIR.Temp t) e acc  in
  let arg_insts_acc = List.fold_left ~init:acc ~f:munch_into_temps temps_exps in
  (QWT.Call { fn_label ; dest }) :: arg_insts_acc

let munch_alloc_array_acc_safe (alloc_arr : T.command) (acc : QWT.instr list) : QWT.instr list =
  (match alloc_arr with 
  | T.Alloc_arr a -> 
    let count_temp_base = Temp.create () in
    let count_temp = STIR.Temp { temp = count_temp_base ; size = A.S_32 } in
    let count_temp_q = STIR.Temp { temp = count_temp_base ; size = A.S_64 } in
    let arr_len_bytes_no_size = STIR.Temp ({ temp = Temp.create () ; size = A.S_64 }) in
    let arr_len_bytes = STIR.Temp ({ temp = Temp.create () ; size = A.S_64 }) in 
    let param_temp_count : A.sized_temp = { temp = Temp.create () ; size = A.S_64 } in
    let param_temp_size : A.sized_temp = { temp = Temp.create () ; size = A.S_64 } in
    let calloc_ret_sized_temp : A.sized_temp = { temp = Temp.create () ; size = A.S_64 } in 
    let calloc_ret_temp = STIR.Temp calloc_ret_sized_temp in
    let count_pos_lbl = Local_label.create () |> AL.Local_label in
    
    let acc0 = munch_exp_pure_acc count_temp a.count acc in
    let acc1 =
      (QWT.If
        { op = LessThan ; lhs = count_temp ; rhs = STIR.Imm32 Int32.zero 
        ; if_true = AL.MEM_LABEL ; if_false = count_pos_lbl })
      :: acc0
    in
    let acc5 = (QWT.Label count_pos_lbl) :: acc1 in 
    let acc6 = (QWT.Unop { op = A.MOVSXD ; src = count_temp ; dest = count_temp_q }):: acc5 in
    let acc7 = 
      (QWT.Binop 
        { op = A.Mul ; lhs = STIR.Imm64 (Int64.of_int a.typ_size) ; rhs = count_temp_q 
        ; dest = arr_len_bytes_no_size }) :: acc6 in
    let acc8 = 
      (QWT.Binop 
        { op = A.Add ; lhs = STIR.Imm64 (Int64.of_int A.word_size) ; rhs = arr_len_bytes_no_size 
        ; dest = arr_len_bytes }) :: acc7 in
    let acc9 = (QWT.Mov { src = arr_len_bytes ; dest = STIR.Temp param_temp_count }) :: acc8 in
    let acc10 = (QWT.Mov { src = STIR.Imm64 Int64.one ; dest = STIR.Temp param_temp_size }) :: acc9 in
    let acc11 = 
      munch_fn_call_acc [T.Temp param_temp_count ; T.Temp param_temp_size] (Symbol.symbol "calloc") 
        (Some calloc_ret_sized_temp) acc10 in
    let acc12 = mem_err_if_null (STIR.Temp calloc_ret_sized_temp) acc11 in
    let acc13 = (QWT.Mem_write { src = count_temp_q ; dest = calloc_ret_temp }) :: acc12 in
    (QWT.Binop 
      { op = A.Add ; lhs = STIR.Imm64 (Int64.of_int A.word_size) ; rhs = calloc_ret_temp 
      ; dest = STIR.Temp a.dest }) :: acc13
  | _ -> failwith "not an alloc_array statement")

let munch_alloc_array_acc_unsafe (alloc_arr : T.command) (acc : QWT.instr list) : QWT.instr list =
  (match alloc_arr with 
  | T.Alloc_arr a -> 
    let count_temp_base = Temp.create () in
    let count_temp = STIR.Temp { temp = count_temp_base ; size = A.S_32} in
    let count_temp_q = STIR.Temp ({ temp = count_temp_base ; size = A.S_64 }) in
    let arr_len_bytes = STIR.Temp ({ temp = Temp.create () ; size = A.S_64 }) in 
    let param_temp_count : A.sized_temp = { temp = Temp.create () ; size = A.S_64 } in
    let param_temp_size : A.sized_temp = { temp = Temp.create () ; size = A.S_64 } in
    
    let acc0 = munch_exp_pure_acc count_temp a.count acc in
    let acc1 = ( QWT.Unop { op = A.MOVSXD ; src = count_temp ; dest = count_temp_q }):: acc0 in
    let acc2 = (QWT.Binop (* TODO: this can probably be optimized for l5, leaq if size 4 or 8 *)
      { op = A.Mul ; lhs = STIR.Imm64 (Int64.of_int a.typ_size) ; rhs = count_temp_q 
      ; dest = arr_len_bytes }) :: acc1 in
    let acc3 = (QWT.Mov { src = arr_len_bytes ; dest = STIR.Temp param_temp_count }) :: acc2 in
    let acc4 = (QWT.Mov { src = STIR.Imm64 Int64.one ; dest = STIR.Temp param_temp_size }) :: acc3 in
    munch_fn_call_acc [T.Temp param_temp_count ; T.Temp param_temp_size] (Symbol.symbol "calloc") 
      (Some a.dest) acc4
  | _ -> failwith "not an alloc_array statement")

let munch_arr_acc_addr_acc (arr_acc : T.command) (is_unsafe : bool) (acc : QWT.instr list)
    : QWT.instr list = 
  (match arr_acc with
  | T.Arr_acc_addr a ->
    let arr_addr = STIR.Temp { temp = Temp.create () ; size = A.S_64 } in
    let idx_base = Temp.create () in
    let idx = STIR.Temp { temp = idx_base ; size = A.S_32 } in
    let idx_dist = STIR.Temp ({ temp = Temp.create () ; size = A.S_64 }) in 
    let idx_q = STIR.Temp ({ temp = idx_base ; size = A.S_64 }) in
    let type_size_temp = STIR.Temp { temp = Temp.create () ; size = A.S_64 } in

    let acc0 = munch_exp_pure_acc arr_addr a.arr acc in
    let acc1 = munch_exp_pure_acc idx a.index acc0 in
    let acc14 =
      if is_unsafe then
        acc1
      else
        let size_addr = STIR.Temp { temp = Temp.create () ; size = A.S_64 } in
        let size_val = STIR.Temp { temp = Temp.create () ; size = A.S_32 } in
        let idx_gt_0_lbl = Local_label.create () |> AL.Local_label in
        let idx_lt_size_lbl = Local_label.create () |> AL.Local_label in
        let acc2 = mem_err_if_null arr_addr acc1 in
        let acc3 = (QWT.Binop 
          { op = A.Add ; lhs = arr_addr ; rhs = STIR.Imm64 (Int64.of_int (-8)) ; dest = size_addr }) 
            :: acc2 in
        let acc4 = (QWT.Mem_read { src = size_addr ; dest = size_val }) :: acc3 in
        let acc5 = 
          (QWT.If 
            { op = A.LessThan ; lhs = idx ; rhs = STIR.Imm32 Int32.zero
            ; if_true = AL.MEM_LABEL ; if_false = idx_gt_0_lbl }) 
          :: acc4
        in
        let acc9 = (QWT.Label idx_gt_0_lbl) :: acc5 in
        let acc10 =
          (QWT.If 
            { op = A.GreaterThanEq ; lhs = idx ; rhs = size_val
            ; if_true = AL.MEM_LABEL ; if_false = idx_lt_size_lbl }) 
          :: acc9
        in
        (QWT.Label idx_lt_size_lbl) :: acc10
    in
    let acc15 = ( QWT.Unop { op = A.MOVSXD ; src = idx ; dest = idx_q }) :: acc14 in
    (match A.int_to_addr_mode_scale a.typ_size with
    | Some scale ->
      let base = match arr_addr with Temp t -> t | _ -> failwith "expected a temp" in
      let index = match idx_q with Temp t -> t | _ -> failwith "expected a temp" in
      let disp = Int32.zero in
      let effective_addr = STIR.Addr_mode { base ; index ; scale ; disp } in
      QWT.Unop  { op = A.LEA ; src = effective_addr ; dest = STIR.Temp a.dest} :: acc15
    | None ->
      let acc16 = 
        (QWT.Mov { src = STIR.Imm64 (Int64.of_int a.typ_size) ; dest = type_size_temp }) 
        :: acc15
      in
      let acc17 = (QWT.Binop 
        { op = A.Mul ; lhs = idx_q ; rhs = type_size_temp ; dest = idx_dist }) 
          :: acc16 in
      (QWT.Binop { op = A.Add ; lhs = arr_addr ; rhs = idx_dist ; dest = STIR.Temp a.dest })
      :: acc17)
  | _ -> failwith "not an arr_acc_addr statement")

(* munch_command : T.stm -> QWT.instr list *)
(* munch_command command generates code to execute command *)
(* Accumulator as first parameter for use as HOF purposes *)
let munch_command_acc (acc : QWT.instr list) (is_unsafe : bool) (is_llvm : bool) 
    (command : T.command)  = 
  (match command with
  | T.Move mv -> munch_exp_pure_acc (STIR.Temp mv.dest) mv.src acc
  | T.Binop_impure b -> munch_binop_exp_impure_acc b.lhs b.op b.rhs (STIR.Temp b.dest) acc is_unsafe is_llvm
  | T.If i -> munch_binop_exp_comp_acc (T.If i) acc
  | T.Goto l -> (QWT.Goto (AL.Local_label l)) :: acc
  | T.Fn_Call c -> munch_fn_call_acc c.arg_list c.name c.dest acc
  | T.Label l -> (QWT.Label (AL.Local_label l)) :: acc
  | T.Fn_Label l -> (QWT.Label (AL.Fn_label l)) :: acc
  | T.Return (Some e) -> 
    let ret_temp = STIR.Temp { temp = Temp.create () ; size = size_I_exp_pure e } in
    QWT.Return (Some ret_temp) :: (munch_exp_pure_acc ret_temp e acc)
  | T.Return None ->  QWT.Return None :: acc 
  | T.Alloc a -> 
    let param_temp1 : A.sized_temp = { temp = Temp.create () ; size = A.S_64 } in
    let param_temp2 : A.sized_temp = { temp = Temp.create () ; size = A.S_64 } in
    let acc0 = 
      (QWT.Mov { src = STIR.Imm64 Int64.one ; dest = STIR.Temp param_temp1 }) 
        :: acc in
    let acc1 = 
      (QWT.Mov { src = STIR.Imm64 (Int64.of_int a.typ_size) ; dest = STIR.Temp param_temp2 }) 
        :: acc0 in
    let acc1 =
      munch_fn_call_acc
        [T.Temp param_temp1 ; T.Temp param_temp2] (Symbol.symbol "calloc") (Some a.dest) acc1
    in 
    if is_unsafe then acc1 else mem_err_if_null (STIR.Temp a.dest) acc1
  | T.Alloc_arr a -> if is_unsafe then
      munch_alloc_array_acc_unsafe (T.Alloc_arr a) acc
    else
      munch_alloc_array_acc_safe (T.Alloc_arr a) acc
  | T.Field_acc_addr a ->
    let struct_addr = STIR.Temp ({ temp = Temp.create () ; size = A.S_64 }) in
    let acc0 = munch_exp_pure_acc struct_addr a.struct_ acc in
    let acc1 =
      if is_unsafe then acc0 else mem_err_if_null struct_addr acc0
    in
    let offset_temp = STIR.Temp { temp = Temp.create() ; size = A.S_64 } in
    let acc2 = 
      (QWT.Mov { src = STIR.Imm64 (Int64.of_int a.offset) ; dest = offset_temp }) :: acc1
    in
    (QWT.Binop 
      { op =  A.Add ; dest = STIR.Temp a.dest ; lhs = struct_addr 
      ; rhs = offset_temp }) :: acc2
  | T.Arr_acc_addr a -> munch_arr_acc_addr_acc (T.Arr_acc_addr a) is_unsafe acc
  | T.Unchecked_read m -> 
    let src_temp = STIR.Temp ({ temp = Temp.create () ; size = A.S_64 }) in 
    let acc0 = munch_exp_pure_acc src_temp m.src acc in
    (QWT.Mem_read { src = src_temp ; dest = STIR.Temp m.dest }) :: acc0
  | T.Checked_read s -> 
    let src_temp = STIR.Temp ({ temp = Temp.create () ; size = A.S_64 }) in
    let acc0 =  munch_exp_pure_acc src_temp s.src acc in
    let acc1 = if is_unsafe then
        acc0
      else
        mem_err_if_null src_temp acc0 in
    (QWT.Mem_read {src = src_temp ; dest = STIR.Temp s.dest }) :: acc1
  | T.Unchecked_write m -> 
    let src_temp = STIR.Temp ({ temp = Temp.create () ; size = size_I_exp_pure m.src }) in
    let acc0 = munch_exp_pure_acc src_temp m.src acc in
    (QWT.Mem_write { src = src_temp ; dest = STIR.Temp m.dest }) :: acc0
  | T.Checked_write s ->
    let src_temp = STIR.Temp ({ temp = Temp.create () ; size = size_I_exp_pure s.src }) in   
    let dest_temp = STIR.Temp s.dest in
    let acc0 = munch_exp_pure_acc src_temp s.src acc in
    let acc1 = if is_unsafe then 
       acc0
      else
        mem_err_if_null dest_temp acc0 in
    (QWT.Mem_write {src = src_temp ; dest = dest_temp }) :: acc1
  )
;;

(* To codegen a series of statements, just concatenate the results of
 * codegen-ing each statement. *)
let codegen commands is_unsafe is_llvm = 
  List.rev(List.fold_left ~init:[] ~f:(fun acc -> munch_command_acc acc is_unsafe is_llvm) commands)

let div_mod_shift_expansion (instrs : QWT.program) : QWT.program =
  let rec div_mod_expansion_rec instrs acc =
    match instrs with
    | [] -> acc
    | (QWT.Binop bop) as instr :: rest ->
      let eax = STIR.Reg { reg = RAX ; size = A.S_32 } in
      let edx = STIR.Reg { reg = RDX ; size = A.S_32 } in
      let cl = STIR.Reg { reg = A.RCX ; size = STIR.size_of bop.rhs } in
      let dest = bop.dest in let rhs = bop.rhs in let lhs = bop.lhs in
      (match bop.op with
      | A.Div ->
        QWT.Mov { dest ; src = eax } 
        :: QWT.Binop { op = A.Div ; dest = eax ; lhs = eax ; rhs }
        :: QWT.Unop { op = A.CDQ ;  dest = edx ; src = eax } 
        :: QWT.Mov { dest = eax ; src = lhs} :: acc
        |> div_mod_expansion_rec rest
      | A.Mod  -> 
        QWT.Mov { dest ; src = edx }
        :: QWT.Binop { op = A.Mod ; dest = edx ; lhs = eax ; rhs }
        :: QWT.Unop { op = A.CDQ ;  dest = edx ; src = eax } 
        :: QWT.Mov { dest = eax ; src = lhs } :: acc
        |> div_mod_expansion_rec rest
      | A.LShift | A.RShift ->
        QWT.Binop { op = bop.op ; dest ; lhs ; rhs = cl }
        :: QWT.Mov { dest = cl ; src = rhs } :: acc 
        |> div_mod_expansion_rec rest
      | _ -> div_mod_expansion_rec rest (instr :: acc) )
    | instr :: rest -> div_mod_expansion_rec rest (instr :: acc)
  in
  div_mod_expansion_rec instrs [] |> List.rev

  (* TODO: fix expect test later (maybe) *)
(* ---------------------------------------- EXPECT TESTS  ----------------------------------------*)
(* module AST = Ast
module IR = Ir_trans
let gen_masn ~sym ~exp = AST.Assign { sym ; exp } |> Mark.naked
let gen_mret exp = AST.Return exp |> Mark.naked
let gen_mconst c = Int32.of_int_exn c |> AST.Const |> Mark.naked
let gen_mvar v = AST.Var v |> Mark.naked
let gen_mfdefn ?t ~n ~ps ~b =
  AST.Fdefn { ret_type = t ; ident = n ; param_list = ps ; block = b } |> Mark.naked
let%expect_test "Test ir->quad translation of a program that calls a function foo from main." =
  Temp.reset ();
  let f_name = Symbol.symbol "foo" in 
  let x = Symbol.symbol "x" in
  let t = AST.Int in
  let asn_exp = AST.(Pure { lhs = gen_mvar x ; rhs = gen_mconst 10 ; op = Plus }) |> Mark.naked in
  let asn_and_ret = 
    AST.Block [ gen_masn ~sym:x ~exp:asn_exp ; gen_mret (gen_mvar x |> Some) ] |> Mark.naked
  in
  let main_name = Symbol.symbol "main" in
  let call = AST.Fn_Call { ident = f_name ; arg_list = [gen_mconst 5] } |> Mark.naked in
  let call_and_ret = AST.Block [ gen_mret (Some call) ] |> Mark.naked in
  let ast_program = 
    AST.[ gen_mfdefn ~t:Int ~n:f_name ~ps:[{ type_ = t ; ident = x }] ~b:[asn_and_ret]
        ; gen_mfdefn ~t:Int ~n:main_name ~ps:[] ~b:[call_and_ret] ]
  in
  let gdecl_ctxts = Typechecker.typecheck ast_program in
  let ir_program = IR.translate ast_program gdecl_ctxts in
  let qwt_program = codegen ir_program in 
  prerr_endline (Print_utils.pp_list ~f:QWT.format ~sep:"\n" qwt_program);
  [%expect
    {|
    _c0_foo(%t1):
      %t3 <-- %t1
      %t4 <-- $10
      %t1 <-- %t3 + %t4
      %{ reg = RAX ; size = A.S_32 } <-- %t1
      ret
    _c0_main():
      %t5 <-- $5
      call _c0_foo(%t5)
      %t2 <-- %{ reg = RAX ; size = A.S_32 }
      %{ reg = RAX ; size = A.S_32 } <-- %t2
      ret
  |}]
;; *)
