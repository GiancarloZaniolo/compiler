open Core 

module A = Assem
module AR = Assem240
module L = A.Label
module RR = AR.RISC240_Regalloc
module SIR240 = AR.Stack_Imm_Reg

open AR.RISC240

(* let ret_addr = 6 *)
(* let error_addr = 8 *)
(* let heap_ptr_addr = 10 *)
(* let stop_addr  = 12 *)
(* let stack_start_addr = 65534 *)
(* let lower_mask = 65535 *)

(* TODO: if this is not necessary for upper translation, delete *)
(* let upper_mask = 4294901760 *)
let fill_call_addr = 0

let rr_threeop_to_r240_threeop = function
  | AR.ADD_p -> ADD
  | AR.AND_p -> AND 
  | AR.SUB_p -> SUB 
  | AR.OR_p -> OR 
  | AR.XOR_p -> XOR

let symbol_from_label (label : L.t) = 
  (match label with 
  | L.Fn_label l -> l.name
  | L.Local_label l -> Local_label.name l |> Symbol.symbol
  | L.MEM_LABEL -> Symbol.symbol "_MEM"
  | _ -> sprintf "Two address translation does not support top-level three-address label: `%s`" 
    (L.format_label label) |> failwith
  )

(* Loads lower half of operand and returns a real register *)
let load_lower_acc stir240 dest_reg acc =
  (match stir240 with
  | SIR240.Imm i ->
    (dest_reg,(LI { dest = dest_reg ; imm = Int.bit_and i AR.max_16_bit}) :: acc)
  | SIR240.Reg AR.Reg1 -> (AR.reg1_lower,acc)
  | SIR240.Reg AR.Reg2 -> (AR.reg2_lower,acc)
  (* TODO: see how we can best circumvent constraints of machine \/ *)
  | Stack_Offset i -> 
    (dest_reg,
      (Threeop_imm { op = LW ; dest = dest_reg ; lhs = AR.rsp ; imm = i + AR.lower_offset}) :: acc)) 

let load_upper_acc stir240 dest_reg acc =
  (match stir240 with
  | SIR240.Imm i -> (*TODO: magic numbers*)
    Printf.printf "From %d -> lower %d\n" i (Int.shift_right_logical (i) 16);
    (* TODO: uncomment if there is a bug *)
    (* (dest_reg,(LI { dest = dest_reg ; imm = Int.shift_right_logical (Int.bit_and i upper_mask) 16}) :: acc) *)
    (dest_reg,(LI { dest = dest_reg ; imm = Int.shift_right_logical i 16}) :: acc)
  | SIR240.Reg AR.Reg1 -> (AR.reg1_upper,acc)
  | SIR240.Reg AR.Reg2 -> (AR.reg2_upper,acc)
  (* TODO: see how we can best circumvent constraints of machine \/ *)
  | SIR240.Stack_Offset i -> 
    (dest_reg,(Threeop_imm { op = LW ; dest = dest_reg ; lhs = AR.rsp ; imm = i}) :: acc)) 

let store_lower_acc stir240 src_reg acc = 
  (match stir240 with
  | SIR240.Imm _ -> failwith "You can never have an immediate destination"
  | SIR240.Reg AR.Reg1 -> if AR.equal_risc240_reg src_reg AR.reg1_lower then
      acc
    else
      (Twoop { op = MV ; src = src_reg ; dest = AR.reg1_lower}) :: acc
  | SIR240.Reg AR.Reg2 -> if AR.equal_risc240_reg src_reg AR.reg2_lower then
    acc
  else
    (Twoop { op = MV ; src = src_reg ; dest = AR.reg2_lower}) :: acc
  | SIR240.Stack_Offset i -> 
    (Threeop_imm { op = SW ; dest = AR.rsp ; lhs = src_reg ; imm = i + AR.lower_offset }) :: acc)

let store_upper_acc stir240 src_reg acc = 
  (match stir240 with
  | SIR240.Imm _ -> failwith "You can never have an immediate destination"
  | SIR240.Reg AR.Reg1 -> if AR.equal_risc240_reg src_reg AR.reg1_upper then
      acc
    else
      (Twoop { op = MV ; src = src_reg ; dest = AR.reg1_upper}) :: acc
  | SIR240.Reg AR.Reg2 -> if AR.equal_risc240_reg src_reg AR.reg2_upper then
      acc
    else
      (Twoop { op = MV ; src = src_reg ; dest = AR.reg2_upper}) :: acc
  | SIR240.Stack_Offset i -> 
    (Threeop_imm { op = SW ; dest = AR.rsp ; lhs = src_reg ; imm = i }) :: acc)
  
let load_lowers stir240_l dest_reg_l stir240_r dest_reg_r acc = 
  let (lhs_h,acc1) = load_lower_acc stir240_l dest_reg_l acc in
  let (rhs_h,acc2) = load_lower_acc stir240_r dest_reg_r acc1 in
  (lhs_h,rhs_h,acc2)

let load_uppers stir240_l dest_reg_l stir240_r dest_reg_r acc = 
  let (lhs_h,acc1) = load_upper_acc stir240_l dest_reg_l acc in
  let (rhs_h,acc2) = load_upper_acc stir240_r dest_reg_r acc1 in
  (lhs_h,rhs_h,acc2)

  (* TODO: delete maybe *)
(* let store_lowers stir240_l src_reg_l stir240_r src_reg_r acc = 
  let acc1 = store_lower_acc stir240_l src_reg_l acc in
  store_lower_acc stir240_r src_reg_r acc1

let store_uppers stir240_l src_reg_l stir240_r src_reg_r acc = 
  let acc1 = store_upper_acc stir240_l src_reg_l acc in
  store_lower_acc stir240_r src_reg_r acc1 *)

let pick_dest_reg dest_reg = function
  | SIR240.Reg Reg1 -> AR.reg1_upper 
  | SIR240.Reg Reg2 -> AR.reg2_upper
  | SIR240.Stack_Offset _ -> dest_reg
  | SIR240.Imm _ -> failwith "Immediate should never be destination"

(* let c0_exception_block (int_label : L.t) (acc : instr list) =
  let exception_val = (match int_label with
    | L.ARITH_LABEL -> 1
    | L.MEM_LABEL -> 2
    | _ -> failwith "Not an exception label ") in
  STOP
  :: (Threeop_imm { op = SW ; dest = R0 ; lhs = R1 ; imm = error_addr })
  :: (LI { dest = R1 ; imm = exception_val })
  :: Local_label (L.format_label int_label |> Symbol.symbol)
  :: acc *)

let munch_binop_acc (instr : RR.instr) (acc : instr list) : instr list = 
  (match instr with
  | Binop b -> 
    (match b.op with
    | ADD_p -> (*going for execution speed instead of space*)
      let if_overflow = Local_label.create () in
      let if_overflow_sym = Symbol.symbol (Local_label.name if_overflow) in
      let end_lbl = Local_label.create () in
      let end_lbl_sym = Symbol.symbol (Local_label.name end_lbl) in
      let (lhs_l,rhs_l,acc1) = load_lowers b.rhs AR.mem_reg1 b.lhs AR.mem_reg2 acc in
      let dest_reg_l = pick_dest_reg AR.mem_reg1 b.dest in
      let acc2 = Threeop { op = ADD ; dest = dest_reg_l ; lhs = lhs_l ; rhs = rhs_l } :: acc1 in
      let acc3 = Branch { op = BRV ; dest = Label if_overflow_sym } :: acc2 in
      (* non-overflow case *)
      let acc4 = store_lower_acc b.dest dest_reg_l acc3 in
      let (lhs_h,rhs_h,acc5) = load_uppers b.rhs AR.mem_reg1 b.lhs AR.mem_reg2 acc4 in
      let dest_reg_h = pick_dest_reg AR.mem_reg1 b.dest in
      let acc6 = Threeop { op = ADD ; dest = dest_reg_h ; lhs = lhs_h ; rhs = rhs_h } :: acc5 in
      let acc7 = Branch { op = BRA ; dest = (Label end_lbl_sym) } :: acc6 in
      (* overflow case *)
      let acc8 = Local_label if_overflow_sym :: acc7 in
      let acc9 = store_lower_acc b.dest dest_reg_l acc8 in
      let (lhs_h,rhs_h,acc10) = load_uppers b.rhs AR.mem_reg1 b.lhs AR.mem_reg2 acc9 in
      let acc11 = Threeop { op = ADD ; dest = dest_reg_h ; lhs = lhs_h ; rhs = rhs_h } :: acc10 in
      let acc12 = Threeop_imm { op = ADDI ; dest = dest_reg_h ; lhs = dest_reg_h ; imm = 1 } :: acc11 in
      let acc13 = Local_label end_lbl_sym :: acc12 in
      store_upper_acc b.dest dest_reg_h acc13
    | SUB_p -> (*going  for exectution speed instead of space*)
      let if_overflow = Local_label.create () in
      let if_overflow_sym = Symbol.symbol (Local_label.name if_overflow) in
      let end_lbl = Local_label.create () in
      let end_lbl_sym = Symbol.symbol (Local_label.name end_lbl) in
      let (lhs_l,rhs_l,acc1) = load_lowers b.rhs AR.mem_reg1 b.lhs AR.mem_reg2 acc in
      let dest_reg_l = pick_dest_reg AR.mem_reg1 b.dest in
      let acc2 = Threeop { op = SUB; dest = dest_reg_l ; lhs = lhs_l ; rhs = rhs_l } :: acc1 in
      let acc3 = Branch { op = BRV ; dest = Label if_overflow_sym } :: acc2 in
      (* non-overflow case *)
      let acc4 = store_lower_acc b.dest dest_reg_l acc3 in
      let (lhs_h,rhs_h,acc5) = load_uppers b.rhs AR.mem_reg1 b.lhs AR.mem_reg2 acc4 in
      let dest_reg_h = pick_dest_reg AR.mem_reg1 b.dest in
      let acc6 = Threeop { op = SUB ; dest = dest_reg_h ; lhs = lhs_h ; rhs = rhs_h } :: acc5 in
      let acc7 = Branch { op = BRA ; dest = (Label end_lbl_sym) } :: acc6 in
      (* overflow case *)
      let acc8 = Local_label if_overflow_sym :: acc7 in
      let acc9 = store_lower_acc b.dest dest_reg_l acc8 in
      let (lhs_h,rhs_h,acc10) = load_uppers b.rhs AR.mem_reg1 b.lhs AR.mem_reg2 acc9 in
      let acc11 = Threeop { op = SUB ; dest = dest_reg_h ; lhs = lhs_h ; rhs = rhs_h } :: acc10 in
      let acc12 = Threeop_imm { op = ADDI ; dest = dest_reg_h ; lhs = dest_reg_h ; imm = 65535 } :: acc11 in
      let acc13 = Local_label end_lbl_sym :: acc12 in
      store_upper_acc b.dest dest_reg_h acc13
    | AND_p | OR_p | XOR_p -> 
      let (lhs_h,rhs_h,acc1) = load_uppers b.rhs AR.mem_reg1 b.lhs AR.mem_reg2 acc in
      let dest_reg_h = pick_dest_reg AR.mem_reg1 b.dest in
      let acc2 = Threeop 
        { op = rr_threeop_to_r240_threeop b.op ; dest = dest_reg_h ; lhs = lhs_h ; rhs = rhs_h } :: acc1 in
      let acc3 = store_upper_acc b.dest dest_reg_h acc2 in
      let (lhs_l,rhs_l,acc4) = load_lowers b.rhs AR.mem_reg1 b.lhs AR.mem_reg2 acc3 in
      let dest_reg_l = pick_dest_reg AR.mem_reg1 b.dest in
      let acc5 = Threeop 
        { op = rr_threeop_to_r240_threeop b.op ; dest = dest_reg_l ; lhs = lhs_l ; rhs = rhs_l } :: acc4 in
      store_lower_acc b.dest dest_reg_l acc5)
  | _ -> failwith "Expected binop in binop generation")


let rec munch_if_acc (instr : RR.instr) (acc : instr list) : instr list = 
  (match instr with
  | If i -> 
    (match i.op with
    | A.LessThan -> 
      let chk_lower_bits = Local_label.create () in
      let chk_lower_bits_sym = Symbol.symbol (Local_label.name chk_lower_bits) in
      let (lhs_h,rhs_h,acc1) = load_uppers i.lhs AR.mem_reg1 i.rhs AR.mem_reg2 acc in
      let acc2 = Threeop { op = SLT ; dest = R0 ; lhs = lhs_h ; rhs = rhs_h } :: acc1 in
      let acc3 = Branch { op = BRN ; dest = Label (symbol_from_label i.if_true) } :: acc2 in
      let acc4 = Branch { op = BRZ ; dest = Label chk_lower_bits_sym } :: acc3 in
      let acc5 = Branch { op = BRA ; dest = (Label (symbol_from_label i.if_false))} :: acc4 in
      let acc6 = Local_label chk_lower_bits_sym :: acc5 in
      let (lhs_l, rhs_l, acc7) = load_lowers i.lhs AR.mem_reg1 i.rhs AR.mem_reg2 acc6 in
      let acc8 = Threeop { op = SLT ; dest = R0 ; lhs = lhs_l ; rhs = rhs_l } :: acc7 in
      let acc9 = Branch { op = BRN ; dest = Label (symbol_from_label i.if_true) } :: acc8 in
      Branch { op = BRA ; dest = (Label (symbol_from_label i.if_false))} :: acc9
    | A.LessThanEq -> 
      let chk_lower_bits = Local_label.create () in
      let chk_lower_bits_sym = Symbol.symbol (Local_label.name chk_lower_bits) in
      let (lhs_h, rhs_h,acc1) = load_uppers i.lhs AR.mem_reg1 i.rhs AR.mem_reg2 acc in
      let acc2 = Threeop { op = SLT ; dest = R0 ; lhs = lhs_h ; rhs = rhs_h } :: acc1 in
      let acc3 = Branch { op = BRN ; dest = Label (symbol_from_label i.if_true) } :: acc2 in
      let acc4 = Branch { op = BRZ ; dest = Label chk_lower_bits_sym } :: acc3 in
      let acc5 = Branch { op = BRA ; dest = (Label (symbol_from_label i.if_false))} :: acc4 in
      let acc6 = Local_label chk_lower_bits_sym :: acc5 in
      let (lhs_l, rhs_l, acc7) = load_lowers i.lhs AR.mem_reg1 i.rhs AR.mem_reg2 acc6 in
      let acc8 = Threeop { op = SLT ; dest = R0 ; lhs = lhs_l ; rhs = rhs_l } :: acc7 in
      let acc9 = Branch { op = BRNZ ; dest = Label (symbol_from_label i.if_true) } :: acc8 in
      Branch { op = BRA ; dest = (Label (symbol_from_label i.if_false))} :: acc9
    | A.EqualsTo -> 
      let chk_lower_bits = Local_label.create () in
      let chk_lower_bits_sym = Symbol.symbol (Local_label.name chk_lower_bits) in
      let (lhs_h, rhs_h, acc1) = load_uppers i.lhs AR.mem_reg1 i.rhs AR.mem_reg2 acc in
      let acc2 = Threeop { op = SLT ; dest = R0 ; lhs = lhs_h ; rhs = rhs_h } :: acc1 in
      let acc3 = Branch { op = BRZ ; dest = Label chk_lower_bits_sym } :: acc2 in
      let acc4 = Branch { op = BRA ; dest = (Label (symbol_from_label i.if_false))} :: acc3 in
      let acc5 = Local_label chk_lower_bits_sym :: acc4 in
      let (lhs_l, rhs_l, acc6) = load_lowers i.lhs AR.mem_reg1 i.rhs AR.mem_reg2 acc5 in
      let acc7 = Threeop { op = SLT ; dest = R0 ; lhs = lhs_l ; rhs = rhs_l } :: acc6 in
      let acc8 = Branch { op = BRZ ; dest = Label (symbol_from_label i.if_true) } :: acc7 in
      Branch { op = BRA ; dest = (Label (symbol_from_label i.if_false))} :: acc8
    | A.NotEqualsTo -> 
      let chk_lower_bits = Local_label.create () in
      let chk_lower_bits_sym = Symbol.symbol (Local_label.name chk_lower_bits) in
      let (lhs_h, rhs_h, acc1) = load_uppers i.lhs AR.mem_reg1 i.rhs AR.mem_reg2 acc in
      let acc2 = Threeop { op = SLT ; dest = R0 ; lhs = lhs_h ; rhs = rhs_h } :: acc1 in
      let acc3 = Branch { op = BRZ ; dest = Label chk_lower_bits_sym } :: acc2 in
      let acc4 = Branch { op = BRA ; dest = (Label (symbol_from_label i.if_true))} :: acc3 in
      let acc5 = Local_label chk_lower_bits_sym :: acc4 in
      let (lhs_l, rhs_l, acc6) = load_lowers i.lhs AR.mem_reg1 i.rhs AR.mem_reg2 acc5 in
      let acc7 = Threeop { op = SLT ; dest = R0 ; lhs = lhs_l ; rhs = rhs_l } :: acc6 in
      let acc8 = Branch { op = BRZ ; dest = Label (symbol_from_label i.if_false) } :: acc7 in
      Branch { op = BRA ; dest = (Label (symbol_from_label i.if_true))} :: acc8
    | A.GreaterThan -> munch_if_acc (If { i with op = A.LessThan ; lhs = i.rhs ; rhs = i.lhs }) acc
    | A.GreaterThanEq -> munch_if_acc (If { i with op = A.LessThanEq ; lhs = i.rhs ; rhs = i.lhs }) acc)
  | _ -> failwith "Expected if in if generation")

(* let stackoverflow_exception_block_acc acc = (*TODO: no clue if works*)
  let good_pos = Local_label.create () in
  let good_pos_sym = Symbol.symbol (Local_label.name good_pos) in
  let acc1 = Threeop_imm { op = LW ; dest = AR.mem_reg1 ; lhs = AR.R0 ; imm = heap_ptr_addr } :: acc in
  let acc2 = Threeop { op = SLT ; dest = AR.R0 ; lhs = AR.mem_reg1 ; rhs = AR.rsp } :: acc1 in
  let acc3 = Branch { op = BRN ; dest = Label good_pos_sym } :: acc2 in
  let acc4 = LI { dest = AR.mem_reg2 ; imm = AR.s_overflow_code } :: acc3 in
  let acc5 = STOP :: acc4 in
  let acc6 = Local_label good_pos_sym :: acc5 in
  Branch { op = BRA ; dest = Addr fill_call_addr } :: acc6 *)

  (* ^ Manual function call that checks if there is stackoverflow *)
  (* This will have a label and a "return" *)
  (* This will take no parameters *)
  (* Checks if rsp is bigger than heap pointer *)
  (* If this is not the case, sets stackoverflow exception and stops *)

(* Note: these have to be in order, create_program should only recieve in order components... *)
let arith_error_block = 
  Local_label (Symbol.symbol "ARITH") 
  :: LI { dest = AR.mem_reg1 ; imm = 1}
  :: Threeop_imm { op = SW ; dest = AR.R0 ; lhs = AR.mem_reg1 ; imm = 8}
  :: []

let mem_error_block = 
  Local_label (Symbol.symbol "MEM") 
  :: LI { dest = AR.mem_reg1 ; imm = 2}
  :: Threeop_imm { op = SW ; dest = AR.R0 ; lhs = AR.mem_reg1 ; imm = 8}
  :: []

  (* TODO: all of these blocks must check for overflow if using stack space *)
(* let mult_block = 
  failwith "u" *)

(* let div_block = 
  failwith "u" *)

(* let modulo_block = 
  failwith "u" *)

(* let rshift_block = 
  failwith "u" *)

(* let rshift_unsigned_block = 
  failwith "u" *)

(* let lshift_block = 
  failwith "u" *)

(* let start_block = 
  (* This should set return pos, error pos, to 0 with directives *)
  (* should set rsp with li *)
  (* first instruction should be goto main *)
  failwith "u" *)

(* let calloc = 
  (* literally just call the function calloc for easy integration *)
  (* TODO: check for stackoverflow after allocation complete *)
  failwith "u" *)

  (* this should not be that hard, nothing is like cased on *)
let risc240_gen instr_list = 
  let gen_lines (acc : instr list) (instr : RR.instr) = 
    (match instr with
    | RR.Binop _ -> munch_binop_acc instr acc
    | RR.Mov m -> 
      (*TODO:is this case even useful? ig makes more efficient but code messy *)
      (* TODO: not worth the extra casing but if it is, make a function that specifically
         moves constants to some register *)
      (* (match (m.dest, m.src) with
      | (SIR240.Reg Reg1, SIR240.Imm i) -> 
        LI { dest =  ; imm = i } :: acc
      | (SIR240.Reg Reg2, SIR240.Imm i) -> LI { dest = reg1_lower; imm = i} :: acc
      | _ ->  *)
      let (src_l,acc1) = load_lower_acc m.src AR.mem_reg1 acc in
      let acc2 = store_lower_acc m.dest src_l acc1 in
      let (src_h,acc3) = load_upper_acc m.src AR.mem_reg2 acc2 in
        store_lower_acc m.dest src_h acc3
    | RR.If _ -> munch_if_acc instr acc
    | RR.Call c -> 
      (* TODO: there can be multiple return instructions, fix this *)
      (* load return address to register *)
      let acc1 = LI { dest = AR.mem_reg1 ; imm = fill_call_addr } :: acc in
      (* write return address into source code *)
      let acc2 = Threeop_imm { op = LW ; dest = R0 ; lhs = AR.mem_reg1 ; imm = fill_call_addr } :: acc1 in
      Branch { op = BRA ; dest = Label (Symbol.symbol (L.format_fn_label ~fn_args:false c.fn_label)) } :: acc2
    | RR.Goto g -> Branch { op = BRA ; dest = Label (Symbol.symbol (L.format_label g)) } :: acc
    | RR.Label (L.Local_label l) -> ((Local_label.name l) |> Symbol.symbol |> Local_label) :: acc
    | RR.Label (L.Fn_label l) -> 
      (Fn_label l.name) :: acc
    | RR.Label (ENTRY_LABEL | EXIT_LABEL | ARITH_LABEL | MEM_LABEL) -> 
      failwith "We probably shouldn't see other label types in RISC240_Regalloc"
    | RR.Return _ -> Branch { op = BRA ; dest = Addr 0} :: acc
      (*TODO: temporary, in new function, correctly do all source code rewritings
        - If main, return jump becomes write solution to designated return address, and goto stop_addr
        - otherwise, keep
        * alternatively, could do this behavior in a previous translation step, it is ok if main
           never returns*)
    | RR.STOP -> STOP :: acc
    | RR.Mem_read _ -> failwith "u" (*do it in steps, this comes after function calls work*)
    | RR.Mem_write _ -> failwith "u"
    | RR.Inc_RSP i -> 
      (Threeop_imm { op = ADDI ; dest = AR.rsp ; lhs = AR.rsp ; imm = Int.bit_and i AR.max_16_bit }) :: acc
    (* TODO: fix bug negatives not elaborated *)
    (* TODO: if decrement, and compiling in safe mode, check for stackoverflow *)
    | RR.Directive d -> (Directive d) :: acc
    | RR.Comment _ -> acc) in
  List.fold_left instr_list ~init:[] ~f:gen_lines |> List.rev
(* set all return addresses to 0x000C to start off *)


(* make a function that properly preps stuff, aka sets up all other blocks, places stuff in the right place *)
(* Note: create_program recieves in-order components, subject to change later *)
let create_program (instrs : RR.instr list) : instr list =
  (* TODO: to add in -
     - mem and arith error blocks
      - mem and arith error blocks will probably be elaborated to labels which I will define when I 
         implement division and shifting and memory accesses
      * mem error label is .MEM, must remove ., name arith error similarly *)
  let block_list = 
  [ [Directive " .ORG $0000\n"
    ; Branch { op = BRA ; dest = Label (Symbol.symbol "_c0_main")}] (*NOTE: temporary directive, in future can probably flatten list*)
  ; arith_error_block
  ; mem_error_block
  ; (risc240_gen instrs)] in
  List.concat block_list