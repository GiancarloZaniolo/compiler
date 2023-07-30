
open Core 

module A = Assem
module AR = Assem240
module L = A.Label
module STIR = A.Stack_Temp_Imm_Reg
module STIR240 = AR.Stack_Temp_Imm_Reg
module RWT = AR.RISC240_With_Temps
module CFG = Cfg

(* Match each parameter with its corresponding register or stack position according to my fictional 
   RISC240 ABI *)
(* Register 1: param 1 and return register *)
(* Register 2: param 1 register *)
(* Everything else: Stack *)
let gen_args (param_temps : A.sized_temp list) ~(in_or_out : int -> STIR240.t) : STIR240.t list = 
  let rec gen_args_acc 
      (remaining_params : A.sized_temp list) (remaining_regs : AR.risc240_alloc_reg list) 
      (stack_slots_used : int) (acc : STIR240.t list) =
    (match (remaining_params, remaining_regs) with
    | ([], _) -> acc
    | (_ :: ts, []) -> 
      let acc' = in_or_out stack_slots_used :: acc in
      gen_args_acc ts remaining_regs (stack_slots_used + 1) acc'
    | (_ :: ts, r :: rs) -> 
      let acc' = STIR240.Reg r :: acc in 
      gen_args_acc ts rs stack_slots_used acc'
    ) in
  gen_args_acc param_temps AR.risc240_arg_regs 0 [] |> List.rev 

(* NOTE: This mutates the CFG *)
let translate (cfg : RWT.program CFG.t) : RWT.program CFG.t = 
  (* NOTE: No callee saved in RISC240 :D *)
  (* let callee_save_srcs : STIR240.t list ref = ref [] in
  let callee_save_dests : STIR240.t list ref = ref [] in *)
  let mov_args ~(srcs : STIR240.t list) ~(dests : STIR240.t list) = 
    List.zip_exn srcs dests |> List.map ~f:(fun (src,dest) -> RWT.Mov { src ; dest }) in
  let temps_to_operands (temps : A.sized_temp list) = 
    List.map ~f:(fun t -> STIR240.Temp t.temp) temps in

  let rec translate_block_acc (prog : RWT.instr list) (acc : RWT.program) : RWT.instr list =
    (match prog with
    | [] -> acc
    | (RWT.Label (L.Fn_label cur_fn)) :: instrs -> 
      let arg_dests = temps_to_operands cur_fn.param_temps in
      let arg_srcs = gen_args cur_fn.param_temps ~in_or_out:(fun i -> STIR240.Arg_In_Stack_Idx i) in
      let arg_get_instrs = RWT.Label (L.Fn_label cur_fn) :: (mov_args ~srcs:arg_srcs ~dests:arg_dests) in
      let acc' = List.rev_append arg_get_instrs acc in
      (* callee_save_dests := List.map ~f:(fun r -> STIR240.Reg r)  AR.risc240_callee_saved_regs ; *)
      (* let acc'' = List.rev_append callee_save_instrs acc' in *)

      (* TODO:delete *)
      (* Printf.printf "%s\n%s\n" "coxungus\n"  (Assem240.RISC240_With_Temps.pp_program acc'); *)
      translate_block_acc instrs acc'
    | (RWT.Return ret_opnd_op) :: instrs -> 
      (* NOTE: we do not yet add optional jumps for function returns, that can be delayed until 
         translation to final risc240 *)
      (* NOTE: There are no callee saved registers, all registers are param *)
      (* let srcs = !callee_save_dests in 
      let dests = !callee_save_srcs in 
      let callee_restore_instrs = List.rev_append (mov_args ~srcs ~dests) acc_rev in *)
      (* NOTE: no clue why, but this was originally different, where return was just given its own 
          list. Is there optimization that can be done? *)
      let acc' = (match ret_opnd_op with
      | Some ret_opnd -> 
        (RWT.Return (Some (STIR240.Reg AR.Reg1))) 
        :: (RWT.Mov { src = ret_opnd ; dest = (STIR240.Reg AR.Reg1)})
        :: acc
      | None -> RWT.Return None :: acc) in
      translate_block_acc instrs acc'
    | (RWT.Call c) :: instrs -> 
      let srcs = temps_to_operands c.fn_label.param_temps in
      let dests = gen_args c.fn_label.param_temps ~in_or_out:(fun i -> STIR240.Arg_Out_Stack_Idx i) in
      let arg_set_instrs = mov_args ~srcs ~dests in
      let acc' = (match c.dest with
        | Some t -> 
          (RWT.Mov { src = STIR240.Reg AR.Reg1 ; dest = STIR240.Temp t.temp})
          :: (RWT.Call c)
          :: List.rev_append arg_set_instrs acc
        | None -> (RWT.Call c) :: List.rev_append arg_set_instrs acc) in
      translate_block_acc instrs acc'
    | instr :: instrs -> translate_block_acc instrs (instr :: acc)) in
    (* NOTE: LEA may be added in a future version, but will try to keep simple for now *)

    let translate_block (label : CFG.label) : unit = 
    let new_block = translate_block_acc (CFG.get_data_exn cfg ~label) [] |> List.rev in
    CFG.set_data cfg ~label ~data:new_block in

  CFG.reverse_postorder_forward cfg |> List.iter ~f:translate_block ;
  cfg

(* I have no clue why the original convention_trans moves stuff to rax, but I will try not doing 
   that for this convention trans *)

