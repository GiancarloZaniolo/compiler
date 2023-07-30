(* This module performs liveness analysis for a program *)

open Core

module AS = Assem
module AL = Assem.Label
module QWT = AS.Quad_With_Temps
module STIR = AS.Stack_Temp_Imm_Reg
module Operand_Set = STIR.Hash_set
module Reverse_Control_Flow_Graph = Graph.Make_Hash_Graph(Int)
module RCFG = Reverse_Control_Flow_Graph 

module Label_Map = Hashtbl.Make(AL)

type reg = string

type line =
  { uses : STIR.t list
  ; defines : STIR.t list
  ; live_out : STIR.t list
  ; move : bool
  ; line_number : int
  }

type analysis_line =
  { uses_set : Operand_Set.t 
  ; defines_set : Operand_Set.t
  ; live_out_set : Operand_Set.t
  ; move : bool
  ; line_number : int
  }

let analysis_line_to_line analysis_line =
  { uses = Hash_set.to_list analysis_line.uses_set
  ; defines = Hash_set.to_list analysis_line.defines_set
  ; live_out = Hash_set.to_list analysis_line.live_out_set
  ; move = analysis_line.move
  ; line_number = analysis_line.line_number}
type program = line list

module Print =
struct
  let pp_line (line : line) =
    sprintf "{ uses = %s ; defines = %s ; live_out = %s ; move = %s ; line_number = %d }"
      (Print_utils.pp_list line.uses ~f:(STIR.format_operand))
      (Print_utils.pp_list line.defines ~f:(STIR.format_operand))
      (Print_utils.pp_list line.live_out ~f:(STIR.format_operand))
      (Bool.to_string line.move)
      line.line_number
  ;;

  let pp_program (program : program) = Print_utils.pp_list ~f:pp_line program ~sep:"\n"
end

type allocation = (reg * reg) option
type allocations = allocation list

let params_to_regs (params : AS.sized_temp List.t) : STIR.t List.t =
  List.sub AS.x86_arg_regs ~pos:0 ~len:(min (List.length params) (List.length AS.x86_arg_regs))
  |> List.map ~f:(fun r -> STIR.Reg {reg = r ; size = AS.S_64 })

let program_of_instrs (instrs : QWT.instr list) : program = 
  let num_lines = List.length instrs in
  let empty_line (_ : unit) : analysis_line =
    { uses_set = Operand_Set.create ~growth_allowed:true ()
    ; defines_set = Operand_Set.create ~growth_allowed:true ()
    ; live_out_set = Operand_Set.create ~growth_allowed:true ()
    ; move = false ; line_number = 0 } in
  (* Data structures *)
  let record_array : analysis_line Array.t = Array.create ~len:num_lines (empty_line ()) in
  let rcf_graph : RCFG.t = RCFG.create ~init_capacity:num_lines () in
  let label_to_line_num_map : int Label_Map.t = Label_Map.create ~growth_allowed:true () in
  (* Helper functions *)
  let resize_stir_list (l : STIR.t list) : STIR.t list = List.map l ~f:(STIR.resize_64) in
  let remove_imms_stacks_dups_resize (ops : STIR.t list) : STIR.t list = 
    let is_not_imm_or_stack op = (match op with 
      | STIR.Imm64 _ | STIR.Imm32 _ | STIR.Arg_In_Stack_Idx _| STIR.Arg_Out_Stack_Idx _ -> false
      | _ -> true)
    in
    let filtered = List.filter ~f:is_not_imm_or_stack ops |> List.stable_dedup in
    resize_stir_list filtered
  in
  let set_pred ~line ~pred =
    let _ : RCFG.t = RCFG.add_directed_edge rcf_graph ~src:line ~dest:pred in ()
  in
  let unsized_reg_list_to_opnd_list = List.map ~f:(fun r -> STIR.Reg { reg = r ; size = AS.S_64 } ) in
  let label_to_line_num label = Label_Map.find_exn label_to_line_num_map label in
  (* Init functions *)
  (* TODO: Have to do a first pass to map the labels to know where the jumps go
     This can probably be resolved if we use basic blocks as nodes in the RCF Graph instead.
     That way, we know that the predecessor of a line in the middle of the basic block is the line
     above it, and we only need to track predecessor information for the root nodes. *)
  let rec build_label_map (qwt_prog : QWT.instr list) (line_num : int) : unit =
    match qwt_prog with
    | [] -> ()
    | instr :: rest -> 
      (match instr with 
      | Label label ->
        Label_Map.add_exn label_to_line_num_map ~key:label ~data:line_num
      | _ -> ()) ; 
    build_label_map rest (line_num + 1)
  in
  let rec init_graph_and_records (qwt_prog : QWT.instr list) (line_num : int) : unit =
    match qwt_prog with
    | [] -> ()
    | instr :: rest -> 
      let init_record : analysis_line = match instr with
      | QWT.Binop op ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups_resize [op.lhs ; op.rhs] |> Operand_Set.of_list
        ; defines_set = remove_imms_stacks_dups_resize [op.dest] |> Operand_Set.of_list
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = false 
        ; line_number = line_num }
      | QWT.Unop op -> 
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups_resize [op.src] |> Operand_Set.of_list
        ; defines_set = remove_imms_stacks_dups_resize [op.dest] |> Operand_Set.of_list
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num }
      | QWT.Mov op ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups_resize [op.src] |> Operand_Set.of_list
        ; defines_set = remove_imms_stacks_dups_resize [op.dest] |> Operand_Set.of_list
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = true
        ; line_number = line_num }
      | QWT.If stm ->
        set_pred ~line:(label_to_line_num stm.if_true) ~pred:(line_num) ;
        set_pred ~line:(label_to_line_num stm.if_false) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups_resize [stm.lhs ; stm.rhs] |> Operand_Set.of_list
        ; defines_set = Operand_Set.create ()
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num}
      | QWT.Goto label -> 
        set_pred ~line:(label_to_line_num label) ~pred:(line_num) ;
        { (empty_line ()) with line_number = line_num }
      | QWT.Call _ ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        let caller_saved_operands = unsized_reg_list_to_opnd_list AS.x86_caller_saved_regs in
        { uses_set = Operand_Set.create ()
        ; defines_set = Operand_Set.of_list caller_saved_operands
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num }
      | QWT.Return _ ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        let callee_saved_operands = unsized_reg_list_to_opnd_list AS.x86_callee_saved_regs in
        { uses_set = Operand_Set.of_list callee_saved_operands 
        ; defines_set = Operand_Set.create ~growth_allowed:false ~size:1 ()
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num }
      | QWT.Label (AL.Fn_label f) ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = Operand_Set.create ()
        ; defines_set = 
          List.map ~f:(fun t : AS.sized_temp -> { temp = t.temp ; size = AS.S_64}) f.param_temps 
          |> params_to_regs |> Operand_Set.of_list
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num }
      | QWT.Mem_read op -> 
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups_resize [op.src] |> Operand_Set.of_list
        ; defines_set = remove_imms_stacks_dups_resize [op.dest] |> Operand_Set.of_list
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = true
        ; line_number = line_num }
      | QWT.Mem_write op ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups_resize [op.src ; op.dest] |> Operand_Set.of_list
        ; defines_set = Operand_Set.create ()
        ; live_out_set = Operand_Set.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num } 
      | QWT.Directive _ | QWT.Comment _ | QWT.Label _ ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { (empty_line ()) with line_number = line_num }
      | QWT.Phi _ -> failwith "Phi functions should not be in live info calculation"
      in 
      record_array.(line_num) <- init_record ; 
      init_graph_and_records rest (line_num + 1)
  in
  (* Actual liveness analysis *)
  let rec back_propagate_var (var : STIR.t) (line : int) : unit =
    let cur_record = record_array.(line) in
    let cur_live_out_set = cur_record.live_out_set in
    let defines_set = cur_record.defines_set in
    if Hash_set.mem cur_live_out_set var then ()
    else (
      Hash_set.add cur_live_out_set var ;
      if Hash_set.mem defines_set var then ()
      else RCFG.nbor_list rcf_graph line |> List.iter ~f:(back_propagate_var var))  
  in
  let generate_live_info (_ : unit) : unit =
    for i = 1 to num_lines do
      let cur_line = num_lines - i in
      let uses_set = record_array.(cur_line).uses_set in
      let preds = RCFG.nbor_list rcf_graph cur_line in
      Hash_set.iter uses_set ~f:(fun var -> List.iter preds ~f:(back_propagate_var var))
    done
  in
  build_label_map instrs 0 ;
  (init_graph_and_records instrs) 0 ;
  generate_live_info (); 
  Array.map ~f:analysis_line_to_line record_array |> Array.to_list 
;;


(* ------------------------------------- DATAFLOW FUNCTIONS ------------------------------------- *)

module CFG = Cfg
module VHS = CFG.Vertex.Hash_set
module STIR_set = STIR.Hash_set
module HS = Hash_set

type live_info = STIR_set.t Dataflow.in_out
type uses_defs = { uses : STIR_set.t ; defs : STIR_set.t }

(* -------------------------------------- HELPER FUNCTIONS -------------------------------------- *)
let get_regs_temps_64 (ops : STIR.t list) : STIR.t list = 
  let is_reg_temp op =
    (match op with | STIR.Reg _ | STIR.Temp _ | STIR.Addr_mode _ -> true | _ -> false)
  in
  let map_addr_mode_to_temps addr_mode =
    match addr_mode with
    | STIR.Addr_mode exp -> [ STIR.Temp exp.base ; STIR.Temp exp.index ]
    | op -> [ op ]
  in
  List.filter ~f:is_reg_temp ops |> List.concat_map ~f:map_addr_mode_to_temps |> List.stable_dedup
  |> List.map ~f:STIR.resize_64
;;

let get_uses_defs (instr : QWT.instr) acc =
  let update_uses line_uses = HS.diff line_uses acc.defs |> HS.union acc.uses in
  let update_defs = HS.union acc.defs in
  match instr with
  | QWT.Phi _ -> failwith "Liveness analysis doesn't currently support SSA form (found phi fn)"
  | QWT.Binop op ->
    { uses = get_regs_temps_64 [op.lhs ; op.rhs] |> STIR_set.of_list |> update_uses
    ; defs = get_regs_temps_64 [op.dest] |> STIR_set.of_list |> update_defs }
  | QWT.Unop op -> 
    { uses = get_regs_temps_64 [op.src] |> STIR_set.of_list |> update_uses
    ; defs = get_regs_temps_64 [op.dest] |> STIR_set.of_list |> update_defs }
  | QWT.Mov op ->
    { uses = get_regs_temps_64 [op.src] |> STIR_set.of_list |> update_uses
    ; defs = get_regs_temps_64 [op.dest] |> STIR_set.of_list |> update_defs }
  | QWT.If stm ->
    { acc with uses = get_regs_temps_64 [stm.lhs ; stm.rhs] |> STIR_set.of_list |> update_uses }
  | QWT.Call _ ->
    let caller_saved_operands = List.map ~f:STIR.reg_to_op_64 AS.x86_caller_saved_regs in
    { acc with defs = STIR_set.of_list caller_saved_operands |> update_defs }
  | QWT.Return _ ->
    let callee_saved_operands = List.map ~f:STIR.reg_to_op_64 AS.x86_callee_saved_regs in
    { acc with uses = STIR_set.of_list callee_saved_operands |> update_uses }
  | QWT.Mem_read op -> 
    { uses = get_regs_temps_64 [op.src] |> STIR_set.of_list |> update_uses
    ; defs = get_regs_temps_64 [op.dest] |> STIR_set.of_list |> update_defs }
  | QWT.Mem_write op ->
    { acc with uses = get_regs_temps_64 [op.src ; op.dest] |> STIR_set.of_list |> update_uses }
  | (QWT.Goto _|QWT.Directive _|QWT.Comment _|QWT.Label _) -> acc
;;

let is_move (instr : QWT.instr) : bool =
  match instr with
  | QWT.Phi _ -> failwith "Liveness analysis doesn't currently support SSA form (found phi fn)"
  | QWT.Mov _|QWT.Mem_read _ -> true
  | QWT.If _|QWT.Goto _|QWT.Call _|QWT.Return _|QWT.Binop _|QWT.Unop _|QWT.Mem_write _
  |QWT.Directive _|QWT.Comment _|QWT.Label _ -> false

(* ------------------------------------- ANALYSIS FUNCTIONS ------------------------------------- *)

let live_info_data_flow (cfg : QWT.program CFG.t) : live_info CFG.t =
  let rec create_block_uses_defs_acc (basic_block : QWT.program) (acc : uses_defs): uses_defs =
    match basic_block with
    | [] -> acc
    | instr :: rest -> get_uses_defs instr acc |> create_block_uses_defs_acc rest
  in
  let create_block_uses_defs (basic_block : QWT.program) : uses_defs =
    create_block_uses_defs_acc basic_block { uses = STIR_set.create () ; defs = STIR_set.create () }
  in
  let uses_defs_cfg : uses_defs CFG.t = CFG.map_data ~f:create_block_uses_defs cfg in
  let transfer (label : CFG.label) (live_out : STIR_set.t) =
    let block_uses_defs = CFG.get_data_exn ~label uses_defs_cfg in
    HS.diff live_out block_uses_defs.defs |> HS.union  block_uses_defs.uses
  in
  Dataflow.dataflow_analyze
    uses_defs_cfg
    ~dir:(Dataflow.BACKWARD)
    ~top:(STIR_set.create)
    ~meet:(HS.union)
    ~transfer
    ~v_boundary:(STIR_set.create)
    ~eq:(HS.equal)
;;

let live_info_to_program_cfg
    (quad_cfg : QWT.program CFG.t) (live_info_cfg : live_info CFG.t) : program CFG.t =
  let rec live_info_acc (basic_block : QWT.program) ~(live_out : STIR_set.t) (acc : program) =
    match basic_block with
    | [] -> acc
    | instr :: rest ->
      let empty_uses_defs _ : uses_defs = 
        { uses = STIR_set.create () ; defs = STIR_set.create () }
      in
      let line_uses_defs = get_uses_defs instr (empty_uses_defs ()) in
      let line_live_in = HS.diff live_out line_uses_defs.defs |> HS.union line_uses_defs.uses in
      let line_live_out = live_out in
      let line : line =
        { uses = line_uses_defs.uses |> HS.to_list
        ; defines = line_uses_defs.defs |> HS.to_list
        ; live_out = line_live_out |> HS.to_list
        ; move = is_move instr
        ; line_number = 0 }
      in
      live_info_acc rest ~live_out:line_live_in (line :: acc)
  in
  let merge_fn ~label (basic_block : QWT.program) (live_info : live_info) : program =
    let _ : CFG.label = label in
    live_info_acc (List.rev basic_block) ~live_out:live_info.out_val []
  in
  CFG.merge_data_exn quad_cfg live_info_cfg ~f:merge_fn
;;

(* ------------------------------------- INTERFACE FUNCTION ------------------------------------- *)

let live_info_analysis (cfg : QWT.program CFG.t) : program CFG.t =
  live_info_data_flow cfg |> live_info_to_program_cfg cfg
;;
