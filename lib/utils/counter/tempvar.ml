
module N : Counter.Nameable = 
struct 
  let name_prefix = "$TEMP"
end

include Counter.Make(N)