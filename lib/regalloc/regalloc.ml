(* L4 Compiler
 * Register allocator implementation
 * Author: Giancarlo Zaniolo (gzaniolo)
 * Modified: Elan Biswas
 *  -Added support for new graph type
 *
 * This module takes in a list of instructions and returns a function that maps temps or pre-defined
 * registers to allocated registers or stack spots. Pre-defined registers are always mapped to
 * themselves.
 *)

open Core

module A = Assem
module AL = Assem.Label
module L = Liveinfo
module QWT = A.Quad_With_Temps
module STIR = A.Stack_Temp_Imm_Reg
module SIR = A.Stack_Imm_Reg

module HS = Hash_set
module DL = Doubly_linked
module DL_elt = DL.Elt
module Q = Queue

module OG = Coalesce_graph.Make_Hash_Graph(STIR)
module OM = STIR.Table
module OS = STIR.Hash_set

type color = int
type stir_to_color = color OM.t
module CS = Int.Hash_set (* CS for Color Set *)

type allocation_mapping = STIR.t -> SIR.t 
type fn_to_spill_count = int Symbol.Map.t

(* -------------------------------------- HELPER FUNCTIONS -------------------------------------- *)
let x86_reserved_regs = A.[ R15 ; R14 ; RSP ]

let assignable_regs_64 =
  let if_not_reserved_then_size (reg : A.x86_reg_64) : A.sized_reg Option.t =
    let size = A.S_64 in
    if List.mem x86_reserved_regs reg ~equal:A.equal_x86_reg_64 |> not then Some { reg ; size }
    else None
  in
  List.filter_map ~f:if_not_reserved_then_size A.all_of_x86_reg_64

let get_pre_def_regs graph =
  List.filter 
    ~f:(fun a -> match a with STIR.Reg _ -> true | _ -> false)
    (OG.representatives_list graph)

let is_stir_reg op = match op with STIR.Reg _ -> true | _ -> false

(* ------------------------------------ END HELPER FUNCTIONS ------------------------------------ *)

let create_interf_graph (liveness_info : L.program) (graph : OG.t) : OG.t = 
  let is_not_op (o : STIR.t) (o2 : STIR.t) : bool = (STIR.compare o o2) <> 0 in
  let rec build_graph (prog : L.program) (g_acc : OG.t) =
    match prog with
    | [] -> g_acc
    | line::rest ->
      let interfere g dest =
        let live_out_minus_dest = List.filter ~f:(is_not_op dest) line.live_out in
        let g' = OG.add_vertex g ~v:dest in
        OG.add_nbors g' ~v:dest ~nbors:live_out_minus_dest
      in
      let g_acc' = List.fold ~f:interfere ~init:g_acc line.defines in
      let g_acc' = List.fold ~f:(fun gr v -> OG.add_vertex gr ~v) ~init:g_acc' line.uses in 
      build_graph rest g_acc'
  in
  let graph' = build_graph liveness_info graph in 
  let pre_def_regs = get_pre_def_regs graph' in 
  let graph'' = 
    List.fold ~init:graph' pre_def_regs
      ~f:(fun gr v ->
        OG.add_nbors gr ~v ~nbors:(List.filter ~f:(fun a -> not (STIR.equal a v)) pre_def_regs)) 
  in
  List.fold_left 
    ~f:(fun gr v -> OG.add_nbors gr ~v ~nbors:(OG.representatives_list gr))
    ~init:graph''
    (List.map ~f:(fun r -> STIR.Reg {reg = r ; size = A.S_64}) x86_reserved_regs)

let rec coalesce_graph (liveness_info : L.program) (g : OG.t) : OG.t =
  let num_assignable_regs = List.length assignable_regs_64 in
  let should_coalesce (v1 : STIR.t) (v2 : STIR.t) : bool =
    let deg_v1 = OG.rep_degree_exn g v1 in
    let deg_v2 = OG.rep_degree_exn g v2 in
    let min_deg_v : STIR.t = if deg_v1 < deg_v2 then v1 else v2 in
    let max_deg_v : STIR.t = if deg_v1 < deg_v2 then v2 else v1 in
    let violates_colorability _ v =
      let open Continue_or_stop in
      if OG.rep_degree_exn g v < num_assignable_regs || OG.is_edge g v max_deg_v then
        Continue ()
      else Stop true
    in
    let min_deg_v_nbors = OG.nbor_rep_list_exn g min_deg_v in
    let should_not_coalesce =
      List.fold_until ~f:(violates_colorability) ~init:() ~finish:(fun () -> false) min_deg_v_nbors
    in
    not should_not_coalesce
  in
  match liveness_info with
  | [] -> g
  | line :: lines ->
    (match (line.move, line.uses) with
    | (false, _) | (_, []) -> coalesce_graph lines g
    | (_, src :: []) ->
      (match line.defines with
      | dest :: [] ->
        let dest_rep = OG.get_rep_exn g dest in
        (if not(OG.is_edge g dest src) && should_coalesce dest src then
          let (con, rep) = if is_stir_reg dest_rep then (src, dest) else (dest, src) in
          coalesce_graph lines (OG.coalesce_exn g ~con ~rep)
        else
          coalesce_graph lines g)
      | [] -> g
      | _ -> failwith "Multiple defines in move")
    | _ -> failwith "Multiple sources in move")

type vertex_weight = { vertex : STIR.t ; mutable weight : int }
type weight_bucket = vertex_weight Doubly_linked.t
type weight_tracker =
  { vert2elt : (vertex_weight DL_elt.t) OM.t ; buckets : (weight_bucket Option.t) Array.t }

(* Creates the data structures that will eventually be used in the ordering algorithm. It creates an
   array of "buckets" (linked lists), with all nodes initially placed in the bucket of weight 0, and
   another table containing the linked list nodes for all of a graph's vertices. This is so that if
   a node must have its weight incremented, it can be found in constant time. *)
let create_weight_tracker (vertices : STIR.t List.t) : weight_tracker = 
  let len = List.length vertices in
  let buckets : (weight_bucket Option.t) Array.t = Array.create ~len None in
  let vert2elt = OM.create ~growth_allowed:true ~size:len () in
  let create_vertex_weight (vertex : STIR.t) : vertex_weight = { vertex ; weight = 0 } in
  buckets.(0) <- List.map ~f:create_vertex_weight vertices |> DL.of_list |> Some ;
  let map_vert_to_elt elt = OM.add_exn vert2elt ~key:((DL_elt.value elt).vertex) ~data:(elt) in
  buckets.(0) |> Option.value_exn |> DL.iter_elt ~f:map_vert_to_elt ;
  { vert2elt ; buckets } 

let create_ordering (weight_tracker : weight_tracker) (graph : OG.t) : STIR.t Q.t =
  let vert2elt = weight_tracker.vert2elt in
  let buckets = weight_tracker.buckets in
  let vert_q = Q.create () in 
  let size = OG.num_reps graph in
  let visited_set : OS.t = OS.create ~growth_allowed:true ~size () in 
  let num_remaining = ref(size) in 
  let max_weight = ref(0) in 
  
  let remove_from_tracker vert = 
    let v_elt = OM.find_exn vert2elt vert in 
    let v_weight = DL_elt.value v_elt in
    let bucket = buckets.(v_weight.weight) |> Option.value_exn in 
    DL.remove bucket v_elt ;
    if DL.is_empty bucket then buckets.(v_weight.weight) <- None
  in
  let add_to_tracker vert = 
    let v_weight = OM.find_exn vert2elt vert |> DL_elt.value in
    match buckets.(v_weight.weight) with 
    | None ->
      buckets.(v_weight.weight) <- DL.of_list [ v_weight ] |> Some ;
      let elt = Option.value_exn buckets.(v_weight.weight) |> DL.first_elt |> Option.value_exn in
      OM.set vert2elt ~key:v_weight.vertex ~data:elt
    | Some bucket ->
      let elt = DL.insert_last bucket v_weight in
      OM.set vert2elt ~key:v_weight.vertex ~data:elt
  in    
  let process_vertex (vert : STIR.t) = 
    let update_nbor_if_unvisited nbor =
      if not (HS.mem visited_set nbor) then
        (remove_from_tracker nbor; 
        let nbor_weight = OM.find_exn vert2elt nbor |> DL_elt.value in
        nbor_weight.weight <- nbor_weight.weight + 1;
        add_to_tracker nbor; 
        if nbor_weight.weight > !max_weight then max_weight := nbor_weight.weight;)
    in 
    List.iter ~f:update_nbor_if_unvisited (OG.nbor_rep_list_exn graph vert); 
    remove_from_tracker vert;
    let v_elt = OM.find_exn vert2elt vert |> DL_elt.value in 
    if (Option.is_empty buckets.(v_elt.weight) && v_elt.weight = !max_weight) then 
      while Option.is_empty buckets.(!max_weight) && !max_weight > 0 do 
        max_weight := !max_weight - 1 
      done;
    HS.add visited_set vert ;
    Q.enqueue vert_q vert;
    num_remaining := !num_remaining - 1
  in 
  (* Pre-defined registers need to get the lowest colors so that they don't get spilled *)
  List.iter ~f:process_vertex (get_pre_def_regs graph) ;
  while !num_remaining > 0 do 
    let max_weight_node = Option.value_exn buckets.(!max_weight) |> DL.first |> Option.value_exn in
    process_vertex max_weight_node.vertex
  done;
  vert_q

let color_graph (graph : OG.t) (queue : STIR.t Q.t) : stir_to_color = 
  let vert2color : stir_to_color = OM.create ~growth_allowed:true ~size:(Q.length queue) () in
  let rec get_idx nbor_colors i = if HS.mem nbor_colors i then get_idx nbor_colors (i+1) else i in
  let add_to_set s v = if OM.mem vert2color v then HS.add s (OM.find_exn vert2color v) else () in
  let add_to_coloring cur_vert idx = OM.set vert2color ~key:cur_vert ~data:(idx) in
  while not (Q.is_empty queue) do 
    let cur_vert = Q.dequeue_exn queue in
    let nbor_colors = CS.create () in
    OG.nbor_rep_list_exn graph cur_vert |> List.iter ~f:(add_to_set nbor_colors);
    let idx = get_idx nbor_colors 0 in
    add_to_coloring cur_vert idx ;
    OG.constituents_list_exn graph cur_vert |> List.iter ~f:(fun v -> add_to_coloring v idx) ;
  done;
  vert2color

let create_allocation_mapping (stir_to_color : stir_to_color) : allocation_mapping = 
  let biggest_color =
    List.fold_right ~f:(fun (_, c1) c2 -> Int.max c1 c2) (OM.to_alist stir_to_color) ~init:0
  in
  let num_colors = biggest_color + 1 in
  let color_to_sir_arr =
    Array.create ~len:num_colors (SIR.Stack_Offset { idx = 0 ; size = A.S_64 })
  in
  let pre_def_stir_regs = OM.keys stir_to_color |> List.filter ~f:is_stir_reg in
  let stir_reg_to_reg = function | STIR.Reg x -> x | _ -> failwith "Expected a register" in
  let map_color_to_reg (reg : STIR.t) : unit = 
    let reg_color = OM.find_exn stir_to_color reg in
    color_to_sir_arr.(reg_color) <- stir_reg_to_reg reg |> SIR.Reg ;
  in
  List.iter ~f:map_color_to_reg pre_def_stir_regs ;
  let pre_def_regs = List.map ~f:stir_reg_to_reg pre_def_stir_regs in
  let is_not_predef reg = not (List.mem pre_def_regs reg ~equal:A.equal_sized_reg) in
  let remaining_sir_regs = Q.create () in 
  List.filter ~f:is_not_predef assignable_regs_64
  |> List.iter ~f:(fun r -> Q.enqueue remaining_sir_regs (SIR.Reg r)) ;
  let cur_spill_idx = ref(0) in
  let assign_color c = function
    | SIR.Stack_Offset _ ->
      let assignment =
        (if Q.is_empty remaining_sir_regs then
          let idx = !cur_spill_idx in
          cur_spill_idx := !cur_spill_idx + 1 ;
          SIR.Stack_Offset { idx = (A.word_size * idx) ; size = A.S_64 }
        else Q.dequeue_exn remaining_sir_regs)
      in
      color_to_sir_arr.(c) <- assignment
    | _ -> () (* Already assigned to a register *)
  in
  Array.iteri ~f:assign_color color_to_sir_arr;
  let temp_to_stack_or_reg = function
    | STIR.Temp t as stir ->
      let stir_64 = STIR.resize_64 stir in
      (match color_to_sir_arr.(OM.find_exn stir_to_color stir_64) with
      | SIR.Reg r -> SIR.Reg { reg = r.reg ; size = t.size }
      | SIR.Stack_Offset s -> SIR.Stack_Offset { idx = s.idx ; size = t.size }
      | SIR.Imm32 _ | SIR.Imm64 _ | SIR.Addr_mode _ -> failwith "found illegal temp type")
    | STIR.Reg r -> SIR.Reg r
    | _ -> failwith "Temp to register function an immediate temp"
  in
  temp_to_stack_or_reg
;;

let generate_fn_to_spill_count
    (program : QWT.instr list) (stir_to_color : stir_to_color) : fn_to_spill_count = 
  let rec set_spill_count s fn operand =
    (match operand with
    | STIR.Reg _ | STIR.Temp _ ->
      let num_regs = A.all_of_x86_reg_64 |> List.length in
      let cur_color = OM.find_exn stir_to_color operand in
      let cur_spill_count = Symbol.Map.find_exn s fn in
      Symbol.Map.set s ~key:fn ~data:(Int.max cur_spill_count (cur_color + 1 - num_regs))
    | STIR.Addr_mode exp ->
      let s' = set_spill_count s fn (STIR.Temp exp.base) in
      set_spill_count s' fn (STIR.Temp exp.index)
    | STIR.Arg_Out_Stack_Idx _ -> s
    | STIR.Arg_In_Stack_Idx _ | STIR.Imm32 _ | STIR.Imm64 _ ->
      failwith "Destination operand shouldn't be an immediate or an argument passed into callee")
  in
  let aggregate_counts (s, cur_fn_opt) instr  =
    let get_fn _ = Option.value_exn cur_fn_opt in
    let update_s dest = set_spill_count s (get_fn ()) (STIR.resize_64 dest), cur_fn_opt in
    match instr with
    | QWT.Binop b -> update_s b.dest
    | QWT.Unop u -> update_s u.dest
    | QWT.Mov m -> update_s m.dest
    | QWT.Mem_read m -> update_s m.dest 
    | QWT.Mem_write m -> update_s m.dest
    | QWT.Label (AL.Fn_label f) -> (Symbol.Map.add_exn s ~key:f.name ~data:0, Some f.name)
    | QWT.Directive _ | Return _ | If _ | Call _ | Goto _ | Label _ | Comment _ -> (s, cur_fn_opt)
    | QWT.Phi _ -> failwith "Phi functions should never be in regalloc" 
  in
  let (result, _) = List.fold_left ~f:aggregate_counts ~init:(Symbol.Map.empty, None) program  in
  result
;;

(* ------------------------------------- INTERFACE FUNCTION  -------------------------------------*)

let generate_mapping_common program liveness_info ~coalesce = 
  let coalesce_if_requested g = if coalesce then coalesce_graph liveness_info g else g in
  let interf_graph =  create_interf_graph liveness_info (OG.create ()) |> coalesce_if_requested in 
  let weight_tracker = create_weight_tracker (OG.representatives_list interf_graph) in
  let vert_q = create_ordering weight_tracker interf_graph in
  let stir_to_color = color_graph interf_graph vert_q in 
  (create_allocation_mapping stir_to_color, generate_fn_to_spill_count program stir_to_color)

let generate_mapping program ~coalesce =
  let liveness_info = L.program_of_instrs program in
  generate_mapping_common program liveness_info ~coalesce

module CFG = Cfg
let generate_mapping_cfg (cfgs : QWT.program CFG.program) ~coalesce =
  let cons_to list a = a :: list in
  let liveness_info = 
    List.fold cfgs ~f:(fun acc cfg -> L.live_info_analysis cfg |> cons_to acc) ~init:[]
    |> List.concat_map ~f:Cfg_trans.list_cfg_to_list
  in
  let program = List.concat_map ~f:Cfg_trans.list_cfg_to_list cfgs in
  generate_mapping_common program liveness_info ~coalesce
