(* TODO: write description *)
open Core

module CFG = Cfg
module AS = Assem
module QWT = Assem.Quad_With_Temps
module STIR = Assem.Stack_Temp_Imm_Reg
module SHT = STIR.Table
module SHS = STIR.Hash_set
module HS = Hash_set

type env = { copy_to_src : STIR.t SHT.t ; src_to_copies : SHS.t SHT.t }

let cp_basic_blocks
    (cfg : QWT.program CFG.t) ~(copy_regs : bool) : QWT.program CFG.t =
  let rec propagate_block_acc (instrs : QWT.program) (env : env) (acc : QWT.program) =
    let get_copy_or_self stir =
      match SHT.find env.copy_to_src stir with Some opnd -> opnd | None -> stir
    in
    let unset_copies stir =
      let copies = SHT.find_or_add env.src_to_copies stir ~default:(SHS.create) in
      HS.iter copies ~f:(SHT.remove env.copy_to_src)
    in
    let add_copy ~src ~copy =
      let copies = SHT.find_or_add env.src_to_copies src ~default:(SHS.create) in
      SHT.set env.copy_to_src ~key:copy ~data:src ;
      HS.add copies copy
    in
    match instrs with
    | [] -> acc
    | [ QWT.If i ] ->
      let lhs' = get_copy_or_self i.lhs in
      let rhs' = get_copy_or_self i.rhs in
      QWT.If { i with lhs = lhs' ; rhs = rhs' } :: acc
    | [ Return (Some ret_opnd) ] ->
      let ret_opnd' = get_copy_or_self ret_opnd in
      Return (Some ret_opnd') :: acc
    | [ (Return None) as instr ] | [ QWT.Goto _ as instr ] -> instr :: acc
    | (QWT.If _|QWT.Goto _|Return _) :: instr :: _ ->
      sprintf "Unexpected instruction in basic block after a jump or return: `%s`"
        (QWT.format instr)
      |> failwith
    | QWT.Mov mov :: rest ->
      unset_copies mov.dest ;
      let src' = get_copy_or_self mov.src in
      let can_copy_src =
        (match src' with
        | STIR.Imm64 imm64 ->
          (* MOVQ is the only x86-64 instruction that allows 64-bit immediates. There is no point
             in constant propagating an imm64 to other moves, and we can't propagate them to any
             other instruction, so we don't propagate them at all. *)
          Int64.(of_int32_exn (Int32.min_value) < imm64 && imm64 < of_int32_exn (Int32.max_value))
        | STIR.Reg _ -> copy_regs 
        | STIR.Addr_mode _ -> false (* Unless we have alias analysis *)
        | (STIR.Temp _ | STIR.Imm32 _ | STIR.Arg_In_Stack_Idx _ | STIR.Arg_Out_Stack_Idx _) -> true
        )
      in
      ( if can_copy_src then add_copy ~src:src' ~copy:mov.dest ) ;
      QWT.Mov { mov with src = src' } :: acc |> propagate_block_acc rest env
    | QWT.Binop bop :: rest ->
      let lhs' = get_copy_or_self bop.lhs in
      let rhs' = get_copy_or_self bop.rhs in
      SHT.remove env.copy_to_src bop.dest ;
      unset_copies bop.dest ;
      QWT.Binop { bop with lhs = lhs' ; rhs = rhs'} :: acc |> propagate_block_acc rest env
    | QWT.Unop uop :: rest ->
      let src' =
        (match get_copy_or_self uop.src with
        | (STIR.Temp _ | STIR.Reg _ | STIR.Arg_In_Stack_Idx _ | STIR.Arg_Out_Stack_Idx _
          |STIR.Addr_mode _) as o -> o
        | (STIR.Imm32 _ | STIR.Imm64 _) -> uop.src)
      in
      SHT.remove env.copy_to_src uop.dest ;
      unset_copies uop.dest ;
      QWT.Unop { uop with src = src' } :: acc |> propagate_block_acc rest env
    | (QWT.Mem_read load) as instr :: rest ->
      SHT.remove env.copy_to_src load.dest ;
      unset_copies load.dest ;
      propagate_block_acc rest env (instr :: acc)
    | (QWT.Call _) as instr :: rest ->
      let caller_save_stirs = List.map AS.x86_caller_saved_regs ~f:STIR.reg_to_op_64 in
      List.iter ~f:unset_copies caller_save_stirs ;
      List.iter ~f:(SHT.remove env.copy_to_src) caller_save_stirs ;
      propagate_block_acc rest env (instr :: acc)
    | (QWT.Comment _|QWT.Directive _|QWT.Mem_write _|QWT.Label _|QWT.Phi _)
      as instr :: rest -> propagate_block_acc rest env (instr :: acc)
  in
  let propagate_block (block : QWT.program) : QWT.program =
    propagate_block_acc block { copy_to_src = SHT.create () ; src_to_copies = SHT.create () } []
    |> List.rev
  in
  CFG.map_data cfg ~f:propagate_block
