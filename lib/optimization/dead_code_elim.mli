(* Interface for Dead Code Elimination. This currently only contains a simple function for removing
 * basic blocks containing nothing but a jump.
 *
 * Author: Elan Biswas <elanb@andrew.cmu.edu>
 *)

val clean_control_flow : Assem.Quad_With_Temps.program Cfg.t -> unit

val remove_dead_phi_srcs :
    Assem.Quad_With_Temps.program Cfg.t -> Assem.Quad_With_Temps.program Cfg.t

(* Aggressive Deadcode Elimination *)
val adce : Assem.Quad_With_Temps.program Cfg.t -> (Symbol.t -> bool) -> unit
