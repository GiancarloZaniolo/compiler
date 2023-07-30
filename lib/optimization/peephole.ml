(* Peephole Optimizations
 * - Constant folding:
 *  - single binary arithmetic instructions
 *  - turning conditional jumps into unconditional jumps 
 * - Strength reductions:
 *  - a * 0 ==> 0 and 0 * a ==> 0
 *  - a * 2^k ==> a << k and 2^k * a ==> a << k
 *  - a + 0 ==> a and 0 + a ==> a and a - 0 ==> a
 *  - a / 1 ==> a
 *  - Expansion of a / 2^k to a combination of >> and +
 * Author: Elan Biswas <elanb@andrew.cmu.edu>
 *)
open Core

module AS = Assem
module AL = Assem.Label
module CFG = Cfg
module QWT = AS.Quad_With_Temps
module QR = AS.Quad_Regalloc
module STIR = AS.Stack_Temp_Imm_Reg
module SIR = AS.Stack_Imm_Reg

let bit_width_32 = Int32.of_int_exn 32

let arith_op_to_math32 = function
  | AS.Add -> Int32.(+)
  | AS.Sub -> Int32.(-)
  | AS.Mul -> Int32.( * )
  | AS.LShift -> (fun n s -> Int32.shift_left n (Int32.to_int_exn s))
  | AS.RShift -> fun n s -> Int32.shift_right n (Int32.to_int_exn s)
  | AS.RShift_unsigned -> fun n s -> Int32.shift_right_logical n (Int32.to_int_exn s)
  | AS.Div ->
    fun n d ->
      if (Int32.(n = Int32.min_value) && Int32.(d = minus_one)) then raise Division_by_zero
      else Int32.(n / d)
  | AS.Mod ->
    fun n d ->
      if (Int32.(n = Int32.min_value) && Int32.(d = minus_one)) then raise Division_by_zero
      else Int32.(rem n d)
  | BWXor -> Int32.bit_xor
  | BWAnd -> Int32.bit_and
  | BWOr -> Int32.bit_or

let arith_op_to_math64 = function
  | AS.Add -> Int64.(+)
  | AS.Sub -> Int64.(-)
  | AS.Mul -> Int64.( * )
  | AS.LShift -> (fun n s -> Int64.shift_left n (Int64.to_int_exn s))
  | AS.RShift -> fun n s -> Int64.shift_right n (Int64.to_int_exn s)
  | AS.RShift_unsigned -> fun n s -> Int64.shift_right_logical n (Int64.to_int_exn s)
  | AS.Div ->
    fun n d ->
      if (Int64.(n = Int64.min_value) && Int64.(d = minus_one)) then raise Division_by_zero
      else Int64.(n / d)
  | AS.Mod ->
    fun n d ->
      if (Int64.(n = Int64.min_value) && Int64.(d = minus_one)) then raise Division_by_zero
      else Int64.(rem n d)
  | BWXor -> Int64.bit_xor
  | BWAnd -> Int64.bit_and
  | BWOr -> Int64.bit_or

let comp_op_to_math32 = function
  | AS.LessThan -> Int32.(<)
  | AS.LessThanEq -> Int32.(<=)
  | AS.GreaterThan -> Int32.(>)
  | AS.GreaterThanEq -> Int32.(>=)
  | AS.EqualsTo -> Int32.(=)
  | AS.NotEqualsTo -> Int32.(<>)

let comp_op_to_math64 = function
  | AS.LessThan -> Int64.(<)
  | AS.LessThanEq -> Int64.(<=)
  | AS.GreaterThan -> Int64.(>)
  | AS.GreaterThanEq -> Int64.(>=)
  | AS.EqualsTo -> Int64.(=)
  | AS.NotEqualsTo -> Int64.(<>)

let compare_imms op imm1 imm2 =
  match (imm1, imm2) with
  | (STIR.Imm32 imm1, STIR.Imm32 imm2) -> comp_op_to_math32 op imm1 imm2
  | (STIR.Imm64 imm1, STIR.Imm64 imm2) -> comp_op_to_math64 op imm1 imm2
  | _ ->
    sprintf "Expected two immediate operands of the same size. Got `%s` and `%s`"
      (STIR.format_operand imm1)
      (STIR.format_operand imm2)
    |> failwith

let floor_ceil_log2 argument =
  match argument with
  | STIR.Imm32 imm ->
    if Int32.(imm <> min_value) then Int32.(floor_log2 (abs imm), ceil_log2 (abs imm))
    else (Int32.num_bits - 1, Int32.num_bits - 1)
  | STIR.Imm64 imm ->
    if Int64.(imm <> min_value) then Int64.(floor_log2 (abs imm), ceil_log2 (abs imm))
    else (Int64.num_bits - 1, Int64.num_bits - 1)
  | _ -> failwith "Expected a constant"

let peep_binop
    (op : AS.quad_arith_binop) ~(dest : STIR.t) ~(lhs : STIR.t) ~(rhs : STIR.t) (acc : QWT.program)
    : QWT.program =
  let original_instr = QWT.Binop { op ; lhs ; rhs ; dest } in
  let peep_div _ =
    match (lhs, rhs) with
    | (_, STIR.Temp _) -> original_instr :: acc
    | (STIR.Reg _, STIR.Imm32 divisor) | (STIR.Temp _, STIR.Imm32 divisor) ->
      if (Int32.to_int_exn divisor = 1) then QWT.Mov { dest ; src = lhs } :: acc
      else if (Int32.to_int_exn divisor = 0) then raise Division_by_zero
      (* In order to turn the division into a shift, we have to do range analysis to ensure that
         an arithmetic exception is not generated *)
      else if (Int32.to_int_exn divisor <> -1) then
      ( let (floor_log2, ceil_log2) = floor_ceil_log2 rhs in
        let t = STIR.Temp { temp = Temp.create () ; size = AS.S_32 } in
        (* Div->Right-shift reduction algorithm from Hacker's Delight, 2nd Edition Chapter 10.1 *)
        if floor_log2 = ceil_log2 then (
          let k = Int32.of_int_exn floor_log2 in
          let acc' =
            QWT.Binop { op = AS.RShift ; dest ; lhs = t ; rhs = STIR.Imm32 k }
            :: QWT.Binop { op = AS.Add ; dest = t ; lhs ; rhs = t }
            :: QWT.Binop
              { op = AS.RShift_unsigned
              ; dest = t ; lhs = t ; rhs = STIR.Imm32 Int32.(bit_width_32 - k) }
            :: QWT.Binop { op = AS.RShift ; dest = t ; lhs ; rhs = STIR.Imm32 Int32.(k - one) }
            :: acc
          in
          if Int32.to_int_exn divisor < 0 then
            QWT.Binop { op = AS.Sub ; dest ; rhs = dest ; lhs = STIR.Imm32 Int32.zero } :: acc'
          else
            acc'
        )
        else original_instr :: acc
      )
      else original_instr :: acc
    | _ ->  original_instr :: acc
  in 
  match (op, lhs, rhs) with
  (* Constant folding single-instruction binop *)
  | (_, STIR.Imm32 lhsi, STIR.Imm32 rhsi) ->
      QWT.Mov { dest ; src = STIR.Imm32 (arith_op_to_math32 op lhsi rhsi) } :: acc
  | (_, STIR.Imm64 lhsi, STIR.Imm64 rhsi) ->
      QWT.Mov { dest ; src = STIR.Imm64 (arith_op_to_math64 op lhsi rhsi) } :: acc
  (* Strength reduce additive identity *)
  | (AS.Add, STIR.Imm32 imm, not_imm) | (AS.Add, not_imm, STIR.Imm32 imm)
  | (AS.Sub, not_imm, STIR.Imm32 imm) ->
    if (Int32.to_int_exn imm = 0) then QWT.Mov { dest ; src = not_imm } :: acc
    else original_instr :: acc
  | (AS.Add, STIR.Imm64 imm, not_imm) | (AS.Add, not_imm, STIR.Imm64 imm) 
  | (AS.Sub, not_imm, STIR.Imm64 imm) ->
    if (Int64.to_int_exn imm = 0) then QWT.Mov { dest ; src = not_imm } :: acc
    else original_instr :: acc
  | (AS.Mul, ((STIR.Imm32 imm) as imm_stir), not_imm)
  | (AS.Mul, not_imm, ((STIR.Imm32 imm) as imm_stir)) ->
    (* a * 0 ==> 0 *)
    if (Int32.to_int_exn imm = 0) then QWT.Mov { dest ; src = STIR.Imm32 Int32.zero } :: acc
    (* Multiplicative identity *)
    else if (Int32.to_int_exn imm = 1) then QWT.Mov { dest ; src = not_imm} :: acc
    (* a * 2^n ==> a << n *)
    else
      let (floor_log2, ceil_log2) = floor_ceil_log2 imm_stir in
      if (floor_log2 = ceil_log2) then (
        let shift = 
          QWT.Binop
            { op = AS.LShift
            ; dest ; lhs = not_imm ; rhs = STIR.Imm32 (Int32.of_int_exn floor_log2) }
        in
        if (Int32.to_int_exn imm < 0) then
          QWT.Binop { op = AS.Sub ; dest ; lhs = STIR.Imm32 Int32.zero ; rhs = dest} :: shift :: acc
        else shift :: acc
      )
      else original_instr :: acc
  | (AS.Mul, ((STIR.Imm64 imm) as imm_stir), not_imm) |
    (AS.Mul, not_imm, ((STIR.Imm64 imm) as imm_stir)) ->
    (* a * 0 ==> 0 *)
    if (Int64.to_int_exn imm = 0) then QWT.Mov { dest ; src = STIR.Imm64 Int64.zero } :: acc
    (* Multiplicative identity *)
    else if (Int64.to_int_exn imm = 1) then QWT.Mov { dest ; src = not_imm} :: acc
    (* a * 2^n ==> a << n *)
    else
      let (floor_log2, ceil_log2) = floor_ceil_log2 imm_stir in
      if (floor_log2 = ceil_log2) then (
        let shift = 
          QWT.Binop
            { op = AS.LShift
            ; dest ; lhs = not_imm ; rhs = STIR.Imm64 (Int64.of_int_exn floor_log2) }
        in
        if (Int64.to_int_exn imm < 0) then
          QWT.Binop { op = AS.Sub ; dest ; lhs = STIR.Imm64 Int64.zero ; rhs = dest} :: shift :: acc
        else shift :: acc
      )
      else original_instr :: acc
  | (AS.Add,_,_) | (AS.Sub,_,_) | (AS.Mul, _, _) -> original_instr :: acc
  | (AS.Div, _, _) -> peep_div ()
  | (AS.Mod, _, _)
  | (AS.LShift, _, _)
  | (AS.RShift, _, _)
  | (AS.RShift_unsigned, _, _)
  | (AS.BWXor, _, _)
  | (AS.BWAnd, _, _)
  | (AS.BWOr, _, _) -> original_instr :: acc

let null_sequence_eliminate (program : QR.program) : QR.program =
  let rec elim_acc rest acc =
    match rest with
    | [] -> acc
    | (QR.Binop bop) as instr :: rest ->
      (* R <- R +- 0 | R <- 0 + R | R <- 1 * R | R <- R /* 1 are all self moves *)
      (match (bop.op, bop.dest, bop.lhs, bop.rhs) with
      | (AS.Add, dest, src, SIR.Imm32 imm32) | (AS.Add, dest, SIR.Imm32 imm32, src) 
      | (AS.Sub, dest, src, SIR.Imm32 imm32) ->
        (if (SIR.equal dest src) && Int32.(imm32 = zero) then elim_acc rest acc
        else elim_acc rest (instr :: acc))
      | (AS.Div, dest, src, SIR.Imm32 imm32)| (AS.Mul, dest, src, SIR.Imm32 imm32)
      | (AS.Mul, dest, SIR.Imm32 imm32, src) ->
        (if (SIR.equal dest src) && Int32.(imm32 = one) then elim_acc rest acc
        else elim_acc rest (instr :: acc))
      | _ -> elim_acc rest (instr :: acc))
    | (QR.Mov mov) as instr :: rest ->
      (* Self move elimination *)
      if SIR.equal mov.src mov.dest then elim_acc rest acc
      else elim_acc rest (instr :: acc)
    | ((QR.Goto goto_lbl) as instr1) :: ((QR.Label lbl) as instr2) :: rest ->
      (* GOTO .Lbl followed by .Lbl ==> eliminate GOTO (only do this if done with basic blocks *)
      if AL.equal goto_lbl lbl then elim_acc rest (instr2 :: acc)
      else elim_acc rest (instr2 :: instr1 :: acc)
    | instr :: rest -> elim_acc rest (instr :: acc)
  in
  elim_acc program [] |> List.rev

let peephole_optimize_basic_block
    (program : QWT.program)
    ~(on_cond_fold : remaining_succ:CFG.label -> unit)
    ~(on_arith_exception : unit -> unit)
    ~(null_jump_elim : bool)
    : QWT.program =
  let rec reduce_acc instrs acc =
    match instrs with
    | [] -> acc
    | QWT.Binop bop :: rest ->
      (try
        peep_binop bop.op ~dest:(bop.dest) ~lhs:(bop.lhs) ~rhs:(bop.rhs) acc |> reduce_acc rest
      with Division_by_zero ->
        on_arith_exception () ; QWT.Goto AL.ARITH_LABEL :: acc) 
    | (QWT.If i) as instr :: rest ->
      (match (i.lhs, i.rhs) with
      (* Constant fold conditionals *)
      | (STIR.Imm32 _, STIR.Imm32 _) | (STIR.Imm64 _, STIR.Imm64 _) -> 
        if (compare_imms i.op i.lhs i.rhs) then
          (on_cond_fold ~remaining_succ:i.if_true ;
          reduce_acc rest (QWT.Goto i.if_true :: acc))
        else
          (on_cond_fold ~remaining_succ:i.if_false ;
          reduce_acc rest (QWT.Goto i.if_false :: acc))
      | _ -> reduce_acc rest (instr :: acc))
    | (QWT.Mov mov) as instr :: rest ->
      (* Self move elimination *)
      if STIR.equal mov.src mov.dest then reduce_acc rest acc
      else reduce_acc rest (instr :: acc)
    | ((QWT.Goto goto_lbl) as instr1) :: ((QWT.Label lbl) as instr2) :: rest ->
      (* GOTO .Lbl followed by .Lbl ==> eliminate GOTO (only do this if done with basic blocks *)
      if null_jump_elim && AL.equal goto_lbl lbl then reduce_acc rest (instr2 :: rest)
      else reduce_acc rest (instr2 :: instr1 :: acc)
    | instr :: rest -> reduce_acc rest (instr :: acc)
  in
  reduce_acc program [] |> List.rev

let peephole_optimize_cfg (cfg : QWT.program CFG.t) : unit =
  let on_cond_fold_pred pred ~remaining_succ =
    CFG.succs cfg pred |> List.filter ~f:(Fn.compose not (AL.equal AL.EXIT_LABEL))
    |> List.iter ~f:(fun succ -> CFG.rem_succ ~pred ~succ cfg) ;
    CFG.set_succ cfg ~pred ~succ:remaining_succ
  in
  let on_arith_exception_pred pred _ =
    CFG.succs cfg pred |> List.iter ~f:(fun succ -> CFG.rem_succ cfg ~pred ~succ) ;
    CFG.set_succ cfg ~pred ~succ:(AL.ARITH_LABEL) ;
    if not (CFG.mem_label cfg AL.ARITH_LABEL) then
      (CFG.set_data cfg ~label:(AL.ARITH_LABEL) ~data:[] ;
      CFG.set_succ cfg ~pred:(AL.ARITH_LABEL) ~succ:(AL.EXIT_LABEL))
  in
  let peep_block (label : CFG.label) : unit =
    let block = CFG.get_data_exn cfg ~label in
    let on_cond_fold = on_cond_fold_pred label in
    let on_arith_exception = on_arith_exception_pred label in
    let block' =
      peephole_optimize_basic_block block ~on_cond_fold ~on_arith_exception ~null_jump_elim:false
    in
    CFG.set_data cfg ~label ~data:block'
  in
  CFG.get_all_labels cfg |> List.iter ~f:peep_block ;
  CFG.remove_unreachable_nodes cfg ;
