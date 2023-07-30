(* Defines functor that outputs a nameable counter module (e.g. Temps, Labels) 
 * Author: Elan Biswas (elanb)
 *)

include module type of Counter_intf
module Make (N : Nameable) : S