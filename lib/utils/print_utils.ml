(* Useful printing functions *)

open Core
  let pp_list ~f ?(sep=", ") list = List.map ~f:f list |> String.concat ~sep:sep