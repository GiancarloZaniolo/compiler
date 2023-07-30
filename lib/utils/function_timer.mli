(* Timing functions to help with compiler runtime profiling.
 * Author: Elan Biswas <elanb@andrew.cmu.edu>
 *
 * Segment timer usage:
 * Suppose you have a function that gets called many times and you want to find out the total amount
 * of time spent on a particular segment of the function:
 *
 * let hot_path x y z =
 *   let something1 in
 *   let something2 in
 *   ...
 *   --- Segment of interest start ---  <-- Function_timer.start_timing_segment ~name:"Segment name"
 *   let something 3 in
 *   something 4;
 *   ...
 *   --- Segment of interest end --- <-- Function_timer.stop_timing_segment ~name:"Segment name"
 *   ...
 *
 * If we place `Function_timer.start_timing_segment ~name:"Segment name"` at the start and
 * `Function_timer.stop_timing_segment ~name:"Segment name"` at the end, and we compile with
 * --verbose, the compiler will automatically compute the total time spent on the segment throughout
 * the course of compiling and pretty print it to standard error.
 *)

(* Function wrapper that times the time to compute f(x), returning f(x). *)
val time_f_of_x : f : ('a->'b) -> 'a -> name:string -> 'b

(* Begin timing a segment from where the segment's timer last left off (or 0.0s). *)
val start_timing_segment : name:string -> unit

(* Increment a segment timer with the amount of time elapsed since the last start. *)
val stop_timing_segment : name:string -> unit

(* Pretty prints the total elapsed time for a segment timer *)
val pp_segment_timer : name:string -> string

(* Pretty prints the total elapsed time for all segment timers *)
val pp_segment_timers : unit -> string