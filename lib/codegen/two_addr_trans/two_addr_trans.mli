(* L4 Compiler
 * Generate x86_64 from 3-addr abstract assembly
 *)

module QR = Assem.Quad_Regalloc
module SIR = Assem.Stack_Imm_Reg 

(* Used to generate x86 lines *)
val x86_gen : QR.instr list -> Assem.X86_Assem.x86_instr list
