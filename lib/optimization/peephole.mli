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

module QWT = Assem.Quad_With_Temps
module QR = Assem.Quad_Regalloc

val null_sequence_eliminate : QR.program -> QR.program
val peephole_optimize_cfg : QWT.program Cfg.t -> unit
