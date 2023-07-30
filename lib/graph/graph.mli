(* Graph Library signature 
 * Author: Elan Biswas (elanb)
 *)
open Core

include module type of Graph_intf
module Make_Hash_Graph (H : Hashable.S) : S with type vertex := H.t