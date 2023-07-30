(* Implements the Temporary Register module as a counter 
 * Author: Elan Biswas (elanb)
 *)

module N : Counter.Nameable = 
struct 
  let name_prefix = "%t"
end

include Counter.Make(N)