(* Defines the signature of a nameable counter module (e.g. Temps, Labels) 
 * Author: Elan Biswas (elanb)
 *)

open Core

module type Nameable =
sig
    (* returns the name of the value *)
    val name_prefix : string
end

module type S =
sig
    type t [@@deriving compare, sexp, hash]

    include Comparable.S with type t := t
    include Hashable.S with type t := t 

    (* resets counter value numbering *)
    val reset : unit -> unit

    (* returns a unique new counter value *)
    val create : unit -> t

    (* returns the name of a counter value *)
    val name : t -> string

    (* returns the value corresponding to the given string if one exists *)
    val from_string : string -> t option
end