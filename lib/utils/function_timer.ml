(* Timing functions to help with compiler runtime profiling.
 *
 * One is a function wrapper that times the given function on the given input, outputting the output
 * of the function.
 *)

module Sym = Symbol
module SHT = Sym.Table

type timer = { mutable elapsed : float  ; mutable last_start : float }

(* We use global state so that a bunch of timer bindings don't have to be littered around *)
let segment_timer_lookup :  timer SHT.t = SHT.create ~growth_allowed:true ()

let time_f_of_x ~f x ~name = 
  let t1 = Sys.time () in
  Core.sprintf "%s..." name |> prerr_endline;
  let res = f x in
  Core.sprintf "%s took %fs\n" name (Sys.time() -. t1) |> prerr_endline;
  res

let register_segment_timer ~(name : string) : timer =
  let timer : timer = { elapsed = 0. ; last_start = 0. } in
  SHT.add_exn segment_timer_lookup ~key:(Sym.symbol name) ~data:timer ;
  timer

let get_segment_timer ~(name : string) : timer =
  match SHT.find segment_timer_lookup (Sym.symbol name) with
  | Some timer -> timer
  | None -> register_segment_timer ~name

let start_timing_segment ~name =
  let timer = get_segment_timer ~name in
  timer.last_start <- Sys.time ()

let stop_timing_segment ~name =
  let stop_time = Sys.time () in
  let timer = get_segment_timer ~name in
  timer.elapsed <- timer.elapsed +. (stop_time -. timer.last_start)

let pp_segment_timer ~name =
  Core.sprintf "Total time of %s: %fs" name (get_segment_timer ~name).elapsed

let pp_segment_timers (_ : unit) : string =
  SHT.keys segment_timer_lookup
  |> Print_utils.pp_list ~sep:"\n" ~f:(fun s -> pp_segment_timer ~name:(Symbol.name s))