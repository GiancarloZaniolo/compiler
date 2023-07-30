(* Implements a functor that outputs a nameable counter module (e.g. Temps, Labels) 
 * Author: Elan Biswas (elanb)
 * Based on starter code Temp library authored by:
 *   Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 *   Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 *   Modified: Frank Pfenning <fp@cs.cmu.edu>
 *   Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *   Modified: Alice Rao <alrao@andrew.cmu.edu>
 *)
open Core

include Counter_intf

module Make (N : Nameable) : S =
struct
  type t = int [@@deriving sexp, compare, hash]

  let counter = ref 1
  let reset () = counter := 1

  let create () : t =
    let t = !counter in
    incr counter;
    t
  ;;

  let name t = N.name_prefix ^ string_of_int t 

  let from_string str = 
    let regex =  N.name_prefix ^ "[1-9][0-9]*" |> Str.regexp in
    if Str.string_match regex str 0 then 
      Str.string_after str 2 |> Int.of_string |> Some
    else
      None

  include Comparable.Make (Int)
  include Hashable.Make (Int)
end