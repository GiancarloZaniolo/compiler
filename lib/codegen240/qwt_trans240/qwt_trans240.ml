

open Core 

module A = Assem
module QWT = A.Quad_With_Temps
module STIR = A.Stack_Temp_Imm_Reg
module AR = Assem240
module RWT = AR.RISC240_With_Temps
module STIR240 = AR.Stack_Temp_Imm_Reg
module CFG = Cfg

let stir_to_stir240 = function
  | STIR.Imm32 i -> STIR240.Imm (Int32.to_int_exn i) (*I guess we will find out when this really is an exn*)
  | STIR.Imm64 i -> 
    if Int64.(>) i (Int64.of_int AR.max_16_bit) then
      failwith "No size 64 constant should be larger than 16 bit max"
    else
      STIR240.Imm (Int64.to_int_exn i)
  | STIR.Temp t -> STIR240.Temp t.temp
  | STIR.Reg _ | STIR.Arg_In_Stack_Idx _ | STIR.Arg_Out_Stack_Idx _ | STIR.Addr_mode _ -> 
    failwith "No other operand types should be present in QWT at this time"

let a_binop_to_ar_binop = function
  | A.Add -> AR.ADD_p
  | A.Sub -> AR.SUB_p
  | A.BWXor -> AR.XOR_p
  | A.BWAnd -> AR.AND_p
  | A.BWOr -> AR.OR_p
  | _ -> failwith "Binop does not exist in RWT"

let trans_instr_acc (acc : RWT.instr list) (instr : QWT.instr) : RWT.instr list = 
  let new_instr = (match instr with
  | QWT.Binop b -> (match b.op with 
    | A.Add | A.Sub | A.BWXor | A.BWAnd | A.BWOr -> RWT.Binop 
      { op = a_binop_to_ar_binop b.op
      ; dest = stir_to_stir240 b.dest
      ; lhs = stir_to_stir240 b.lhs
      ; rhs = stir_to_stir240 b.rhs}
    | _ -> failwith "Other binops not yet implemented")
    (* note: rest should be turned into function calls. Also, come up with names for all 
       function call things *)
  | QWT.Unop u -> (match u.op with
    | A.MOVSXD -> RWT.Mov 
      { src = stir_to_stir240 u.src ; dest = stir_to_stir240 u.dest }
    | A.LEA -> failwith "Ideally, there should never be LEA in code destined for RISC240"
    | A.CDQ -> failwith "CDQ should not be present yet in QWT")
  | QWT.Mov m -> RWT.Mov 
  { src = stir_to_stir240 m.src ; dest = stir_to_stir240 m.dest }
  | QWT.Phi _ -> failwith "Phi functions should not be present in code destined for RISC240 " 
  | QWT.If i -> RWT.If
    { op = i.op 
    ; lhs = stir_to_stir240 i.lhs 
    ; rhs = stir_to_stir240 i.rhs
    ; if_true = i.if_true 
    ; if_false = i.if_false }
  | QWT.Call c -> RWT.Call c
  | QWT.Goto g -> RWT.Goto g
  | QWT.Label l -> RWT.Label l
  | QWT.Return r -> RWT.Return (Option.map r ~f:(fun r -> stir_to_stir240 r))
  | QWT.Mem_read m -> RWT.Mem_read 
    { src = stir_to_stir240 m.src ; dest = stir_to_stir240 m.dest ; imm = 0}
  | QWT.Mem_write m -> RWT.Mem_write
    { src = stir_to_stir240 m.src ; dest = stir_to_stir240 m.dest ; imm = 0}
  | QWT.Directive d -> RWT.Directive d
  | QWT.Comment c -> RWT.Comment c ) in
  new_instr :: acc

let qwt_trans_240 (cfg : QWT.program CFG.t) : RWT.program CFG.t = 
  let translate_block (instrs : QWT.program) : RWT.program = 
    List.fold_left ~init:[] ~f:trans_instr_acc instrs |> List.rev in
  CFG.map_data cfg ~f:translate_block

(* TODO: this can probably be made to take leaqs, but do it the simple way first *)
