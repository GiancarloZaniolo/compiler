(* Interface for partial redundancy elimination on a mutable control flow graph.
 * Implemenation from Compilers: Principle, Techniques, and Tools, 2nd Edtion (Purple Dragon Book)
 * Chapter 9.5.
 *
 * Author: Elan Biswas <elanb@andrew.cmu.edu>
 *)
 
 open Core

module AS = Assem
module QWT = Assem.Quad_With_Temps
module STIR = Assem.Stack_Temp_Imm_Reg

module Expression :
sig
    type t = { op : AS.quad_arith_binop ; lhs : STIR.t ; rhs : STIR.t }
      [@@deriving hash, sexp, compare, equal]
  include Hashable.S with type t := t
  include Comparable.S with type t := t

  val pp_expression : t -> string
end

val eliminate_partial_redundancies : QWT.program Cfg.t -> unit
