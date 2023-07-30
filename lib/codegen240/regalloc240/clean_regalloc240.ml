
module L = Assem.Label
module AR = Assem240
module RR = AR.RISC240_Regalloc
module SIR240 = AR.Stack_Imm_Reg


let null_sequence_eliminate (instrs : RR.program) : RR.program = 
  let rec elim_acc rest acc = 
    match rest with
    | [] -> acc 
    | (RR.Binop bop) as instr :: rest -> 
      (match (bop.op, bop.dest, bop.lhs, bop.rhs) with
      | (AR.ADD_p, dest, src, SIR240.Imm imm) | (AR.ADD_p, dest, SIR240.Imm imm, src) 
      | (AR.SUB_p, dest, src, SIR240.Imm imm) ->
        (if (SIR240.equal dest src) && imm = 0 then elim_acc rest acc
        else elim_acc rest (instr :: acc))
      (* | I am too lazy to fix these *)
      (* | Division not a binop in risc240 *)
      (* | Multiplication not a binop in risc240*)
      | _ -> elim_acc rest (instr :: acc))
    | (RR.Mov mov) as instr :: rest ->
      (* Self move elimination *)
      if SIR240.equal mov.src mov.dest then elim_acc rest acc
      else elim_acc rest (instr :: acc)
    | ((RR.Goto goto_lbl) as instr1) :: ((RR.Label lbl) as instr2) :: rest ->
      (* GOTO .Lbl followed by .Lbl ==> eliminate GOTO (only do this if done with basic blocks *)
      if L.equal goto_lbl lbl then elim_acc rest (instr2 :: acc)
      else elim_acc rest (instr2 :: instr1 :: acc)
    | instr :: rest -> elim_acc rest (instr :: acc) in
  elim_acc instrs [] |> List.rev