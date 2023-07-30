(* L4 Compiler
 * Register allocator interface
 * Author: Giancarlo Zaniolo (gzaniolo)
 * Modified: Elan Biswas (elanb)
 *)

(* Maps the original abstract assembly operands to their allocated register counterparts *)
type allocation_mapping = Assem.Stack_Temp_Imm_Reg.t -> Assem.Stack_Imm_Reg.t

(* Maps each function in the program to the number of registers that are spilled to the stack *)
type fn_to_spill_count = int Symbol.Map.t

(* Takes in the list of assembly instructions, returns a function that maps abstract assembly
   register operands to actual registers, as well as the number of temporary registers that spill
   over into the stack. *)
val generate_mapping : 
   Assem.Quad_With_Temps.program -> coalesce:bool -> (allocation_mapping * fn_to_spill_count)

val generate_mapping_cfg :
   Assem.Quad_With_Temps.program Cfg.program
   -> coalesce:bool -> (allocation_mapping * fn_to_spill_count)
