(* Implements the Label module as a counter 
 * Author: Elan Biswas (elanb)
 *)

module N : Counter.Nameable = 
struct 
  let name_prefix = ".L"
end

include Counter.Make(N)