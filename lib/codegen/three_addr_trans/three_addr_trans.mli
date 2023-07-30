(* L4 Compiler
 * Assembly Code Generator for FAKE assembly
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Based on code by: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Implements a "convenient munch" algorithm
 *)

val div_mod_shift_expansion : Assem.Quad_With_Temps.program -> Assem.Quad_With_Temps.program

val codegen : Ir_tree.program -> bool -> bool -> Assem.Quad_With_Temps.instr list
