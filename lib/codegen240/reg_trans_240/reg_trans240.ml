

open Core

module A = Assem
module AR = Assem240
module L = A.Label
module R = Regalloc240
module RWT = AR.RISC240_With_Temps
module RR = AR.RISC240_Regalloc
module STIR240 = AR.Stack_Temp_Imm_Reg
module SIR240 = AR.Stack_Imm_Reg
module SHT = Symbol.Table


(* Regalloc is set up such that the cfg is destroyed when it returns. Because previous code already
     works, it is probably best to keep it this way *)
let generate_fn_to_max_args (program : RWT.instr list) : int SHT.t = 
  let max_arg_map = SHT.create () in
  let aggregate_set curr_fn_opt instr = 
    (match instr with
    | RWT.Label (L.Fn_label f) -> SHT.add_exn max_arg_map ~key:f.name ~data:0; Some f.name
    | RWT.Call c -> 
      let curr_fn = Option.value_exn curr_fn_opt in
      let num_params = List.length c.fn_label.param_temps in
      let max_params = SHT.find_exn max_arg_map curr_fn |> Int.max num_params in
      SHT.set max_arg_map ~key:curr_fn ~data:max_params;
      curr_fn_opt
    | _ -> curr_fn_opt) in
  let _ : Symbol.t Option.t = List.fold_left program ~init:None ~f:aggregate_set in
  max_arg_map

let translate_to_RISC240_regalloc ?(coalesce = false) rwt_instr_list rwt_cfg = 
  (* Generates register allocation mapping *)
  let (temp_to_reg, fn_to_spill_count) = R.generate_mapping_cfg rwt_cfg ~coalesce in
  let fn_to_max_args_ht = generate_fn_to_max_args rwt_instr_list in
  let rec translate_acc (prog : RWT.instr list) (prev_fn : L.fn_label) (acc : RR.instr list) 
      : RR.instr list = 
    let curr_fn = (match prog with | RWT.Label (L.Fn_label f) :: _ -> f | _ -> prev_fn) in
    let max_args = SHT.find_exn fn_to_max_args_ht curr_fn.name in
    let max_stack_args = List.length AR.risc240_arg_regs |> Int.(-) max_args |> Int.max 0 in
    let spill_count = Symbol.Map.find_exn fn_to_spill_count curr_fn.name in 
    let total_used_slots = max_stack_args + spill_count in
    (* TODO: I do not believe we need to 16 byte align stack frames *)
    let num_frame_slots = total_used_slots in (* TODO:delete *)
    let frame_size = num_frame_slots * AR.word_size in
    (* TODO: delete *)
    let _ = frame_size in
    (* NOTE: @@important section here, not done implementing *)
    let rti_to_rsti = function
      | STIR240.Reg _ | STIR240.Temp _ as x -> 
        (match temp_to_reg x with
        | SIR240.Stack_Offset i -> SIR240.Stack_Offset (i + (AR.word_size * max_stack_args))
        | reg -> reg)
      | STIR240.Arg_In_Stack_Idx i -> SIR240.Stack_Offset (AR.word_size * (i + num_frame_slots + 1))
      | STIR240.Arg_Out_Stack_Idx i -> SIR240.Stack_Offset (AR.word_size * i)
      | STIR240.Imm i -> SIR240.Imm i  in
    match prog with
    | [] -> acc
    | line :: lines -> 
      let acc' =
        match line with
        | RWT.Binop b -> 
          RR.Binop { op = b.op ; dest = rti_to_rsti b.dest
                   ; lhs = rti_to_rsti b.lhs ; rhs = rti_to_rsti b.rhs } :: acc
        | RWT.Mov m -> 
          RR.Mov { dest = rti_to_rsti m.dest ; src = rti_to_rsti m.src } :: acc
        | RWT.If i -> 
          RR.If { op = i.op ; lhs = rti_to_rsti i.lhs ; rhs = rti_to_rsti i.rhs
                ; if_true = i.if_true ; if_false = i.if_false } :: acc
        | RWT.Goto l -> (RR.Goto l) :: acc
        | RWT.Call c -> (RR.Call c) :: acc
        | RWT.Label ((L.Fn_label _) as lbl) -> (*TODO: check correctness*)
          RR.Inc_RSP (-frame_size) 
          :: (RR.Label lbl)
          :: acc
        | RWT.Label l -> (RR.Label l) :: acc
        | RWT.Return op_opt -> (*TODO: check_correctness*)
          RR.Return (Option.map ~f:rti_to_rsti op_opt)
          :: RR.Inc_RSP frame_size
          :: acc
        | RWT.Mem_read r -> (RR.Mem_read { dest = rti_to_rsti r.dest ; src = rti_to_rsti r.src ; imm = 0 }) :: acc
        | RWT.Mem_write r -> (RR.Mem_write { dest = rti_to_rsti r.dest ; src = rti_to_rsti r.src ; imm = 0 }) :: acc
        | RWT.Inc_RSP _ -> failwith "Inc_RSP should not be present before reg_trans"
        | RWT.Directive d -> (RR.Directive d) :: acc
        | RWT.Comment _ -> acc
        | RWT.STOP -> RR.STOP :: acc
    in
    translate_acc lines curr_fn acc' 
  in
  (match rwt_instr_list with
  | RWT.Label (L.Fn_label f) :: _ -> translate_acc rwt_instr_list f [] |> List.rev
  |  _ -> failwith "Malformed program, function label not first instruction")




