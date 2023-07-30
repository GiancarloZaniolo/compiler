(* This module performs liveness analysis for a program *)

(* NOTE: Anything sized has been removed for risc240. If needed for tighter register allocation, 
    look to original file for what they did *)
(* If I was good, I would make this all  *)

open Core

module A = Assem
module AR = Assem240
module L = A.Label
module RWT = AR.RISC240_With_Temps
module STIR240 = AR.Stack_Temp_Imm_Reg
module STIR240_HT = STIR240.Hash_set
module RCFG = Graph.Make_Hash_Graph(Int)
module Label_HT = L.Table

type reg = string

type line =
  { uses : STIR240.t list
  ; defines : STIR240.t list
  ; live_out : STIR240.t list
  ; move : bool
  ; line_number : int
  }

type analysis_line =
  { uses_set : STIR240_HT.t 
  ; defines_set : STIR240_HT.t
  ; live_out_set : STIR240_HT.t
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
      (Print_utils.pp_list line.uses ~f:(STIR240.format_operand))
      (Print_utils.pp_list line.defines ~f:(STIR240.format_operand))
      (Print_utils.pp_list line.live_out ~f:(STIR240.format_operand))
      (Bool.to_string line.move)
      line.line_number
  ;;

  let pp_program (program : program) = Print_utils.pp_list ~f:pp_line program ~sep:"\n"
end

type allocation = (reg * reg) option
type allocations = allocation list

let program_of_instrs (instrs : RWT.instr list) : program = 
  let num_lines = List.length instrs in
  let empty_line (_ : unit) : analysis_line =
    { uses_set = STIR240_HT.create ~growth_allowed:true ()
    ; defines_set = STIR240_HT.create ~growth_allowed:true ()
    ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
    ; move = false ; line_number = 0 } in
  (* Data structures *)
  let record_array : analysis_line Array.t = Array.create ~len:num_lines (empty_line ()) in
  let rcf_graph : RCFG.t = RCFG.create ~init_capacity:num_lines () in
  let label_to_line_num_map : int Label_HT.t = Label_HT.create ~growth_allowed:true () in
  (* Helper functions *)
  let remove_imms_stacks_dups (ops : STIR240.t list) : STIR240.t list = 
    let is_not_imm_or_stack op = (match op with 
      | STIR240.Imm _ | STIR240.Arg_In_Stack_Idx _| STIR240.Arg_Out_Stack_Idx _ -> false
      | _ -> true) in
    List.filter ~f:is_not_imm_or_stack ops |> List.stable_dedup 
  in
  let set_pred ~line ~pred =
    let _ : RCFG.t = RCFG.add_directed_edge rcf_graph ~src:line ~dest:pred in ()
  in
  let reg_list_to_opnd_list = List.map ~f:(fun r -> STIR240.Reg r) in
  let label_to_line_num label = Label_HT.find_exn label_to_line_num_map label in
  (* Init functions *)
  (* TODO: Have to do a first pass to map the labels to know where the jumps go
     This can probably be resolved if we use basic blocks as nodes in the RCF Graph instead.
     That way, we know that the predecessor of a line in the middle of the basic block is the line
     above it, and we only need to track predecessor information for the root nodes. *)
  let rec build_label_map (qwt_prog : RWT.instr list) (line_num : int) : unit =
    match qwt_prog with
    | [] -> ()
    | instr :: rest -> 
      (match instr with 
      | Label label ->
        Label_HT.add_exn label_to_line_num_map ~key:label ~data:line_num
      | _ -> ()) ; 
    build_label_map rest (line_num + 1)
  in
  let rec init_graph_and_records (qwt_prog : RWT.instr list) (line_num : int) : unit =
    match qwt_prog with
    | [] -> ()
    | instr :: rest -> 
      let init_record : analysis_line = match instr with
      | RWT.Binop op ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups [op.lhs ; op.rhs] |> STIR240_HT.of_list
        ; defines_set = remove_imms_stacks_dups [op.dest] |> STIR240_HT.of_list
        ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
        ; move = false 
        ; line_number = line_num }
      | RWT.Mov op ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups [op.src] |> STIR240_HT.of_list
        ; defines_set = remove_imms_stacks_dups [op.dest] |> STIR240_HT.of_list
        ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
        ; move = true
        ; line_number = line_num }
      | RWT.If stm ->
        set_pred ~line:(label_to_line_num stm.if_true) ~pred:(line_num) ;
        set_pred ~line:(label_to_line_num stm.if_false) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups [stm.lhs ; stm.rhs] |> STIR240_HT.of_list
        ; defines_set = STIR240_HT.create ()
        ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num}
      | RWT.Goto label -> 
        set_pred ~line:(label_to_line_num label) ~pred:(line_num) ;
        { (empty_line ()) with line_number = line_num }
      | RWT.Call _ ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        let caller_saved_operands = reg_list_to_opnd_list AR.risc240_caller_saved_regs in
        { uses_set = STIR240_HT.create ()
        ; defines_set = STIR240_HT.of_list caller_saved_operands
        ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num }
      | RWT.Return _ ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        let callee_saved_operands = reg_list_to_opnd_list AR.risc240_callee_saved_regs in
        { uses_set = STIR240_HT.of_list callee_saved_operands 
        ; defines_set = STIR240_HT.create ~growth_allowed:false ~size:1 ()
        ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num }
      | RWT.Label (L.Fn_label f) ->
        let params_to_regs (params : A.sized_temp List.t) : STIR240.t List.t =
          List.sub AR.risc240_arg_regs ~pos:0 ~len:(min (List.length params) (List.length AR.risc240_arg_regs))
          |> List.map ~f:(fun r -> STIR240.Reg r) 
        in
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = STIR240_HT.create ()
        ; defines_set = 
          f.param_temps |> params_to_regs |> STIR240_HT.of_list
        ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num }
      | RWT.Mem_read op -> 
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups [op.src] |> STIR240_HT.of_list
        ; defines_set = remove_imms_stacks_dups [op.dest] |> STIR240_HT.of_list
        ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
        ; move = true
        ; line_number = line_num }
      | RWT.Mem_write op ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { uses_set = remove_imms_stacks_dups [op.src ; op.dest] |> STIR240_HT.of_list
        ; defines_set = STIR240_HT.create ()
        ; live_out_set = STIR240_HT.create ~growth_allowed:true ()
        ; move = false
        ; line_number = line_num } 
      | RWT.Directive _ | RWT.Comment _ | RWT.Label _ | RWT.STOP ->
        set_pred ~line:(line_num + 1) ~pred:(line_num) ;
        { (empty_line ()) with line_number = line_num }
      | RWT.Inc_RSP _ -> failwith "Inc_RSP should not be present during liveinfo"
      in 
      record_array.(line_num) <- init_record ; 
      init_graph_and_records rest (line_num + 1)
  in
  (* Actual liveness analysis *)
  let rec back_propagate_var (var : STIR240.t) (line : int) : unit =
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
module STIR240_HS = STIR240.Hash_set
module HS = Hash_set

type live_info = STIR240_HS.t Dataflow.in_out
type uses_defs = { uses : STIR240_HS.t ; defs : STIR240_HS.t }

(* -------------------------------------- HELPER FUNCTIONS -------------------------------------- *)
let get_regs_temps (ops : STIR240.t list) : STIR240.t list = 
  let is_reg_temp op =
    (match op with | STIR240.Reg _ | STIR240.Temp _ -> true | _ -> false)
  in
  List.filter ~f:is_reg_temp ops |> List.stable_dedup 
;;

let get_uses_defs (instr : RWT.instr) acc =
  let update_uses line_uses = HS.diff line_uses acc.defs |> HS.union acc.uses in
  let update_defs = HS.union acc.defs in
  match instr with
  | RWT.Binop op ->
    { uses = get_regs_temps [op.lhs ; op.rhs] |> STIR240_HS.of_list |> update_uses
    ; defs = get_regs_temps [op.dest] |> STIR240_HS.of_list |> update_defs }
  | RWT.Mov op ->
    { uses = get_regs_temps [op.src] |> STIR240_HS.of_list |> update_uses
    ; defs = get_regs_temps [op.dest] |> STIR240_HS.of_list |> update_defs }
  | RWT.If stm ->
    { acc with uses = get_regs_temps [stm.lhs ; stm.rhs] |> STIR240_HS.of_list |> update_uses }
  | RWT.Call _ ->
    let caller_saved_operands = List.map ~f:(fun r -> STIR240.Reg r) AR.risc240_caller_saved_regs in
    { acc with defs = STIR240_HS.of_list caller_saved_operands |> update_defs }
  | RWT.Return _ ->
    let callee_saved_operands = List.map ~f:(fun r -> STIR240.Reg r) AR.risc240_callee_saved_regs in
    { acc with uses = STIR240_HS.of_list callee_saved_operands |> update_uses }
  | RWT.Mem_read op -> 
    { uses = get_regs_temps [op.src] |> STIR240_HS.of_list |> update_uses
    ; defs = get_regs_temps [op.dest] |> STIR240_HS.of_list |> update_defs }
  | RWT.Mem_write op ->
    { acc with uses = get_regs_temps [op.src ; op.dest] |> STIR240_HS.of_list |> update_uses }
  | (RWT.Goto _| RWT.Directive _| RWT.Comment _| RWT.Label _ | RWT.STOP) -> acc
  | RWT.Inc_RSP _ -> failwith "Inc_RSP Should not be present during liveinfo"
;;

let is_move (instr : RWT.instr) : bool =
  match instr with
  | RWT.Mov _| RWT.Mem_read _ -> true
  | RWT.If _| RWT.Goto _| RWT.Call _| RWT.Return _| RWT.Binop _ | RWT.Mem_write _
  | RWT.Directive _| RWT.Comment _| RWT.Label _ | RWT.STOP | RWT.Inc_RSP _ -> false

(* ------------------------------------- ANALYSIS FUNCTIONS ------------------------------------- *)

let live_info_data_flow (cfg : RWT.program CFG.t) : live_info CFG.t =
  let rec create_block_uses_defs_acc (basic_block : RWT.program) (acc : uses_defs): uses_defs =
    match basic_block with
    | [] -> acc
    | instr :: rest -> get_uses_defs instr acc |> create_block_uses_defs_acc rest
  in
  let create_block_uses_defs (basic_block : RWT.program) : uses_defs =
    create_block_uses_defs_acc basic_block { uses = STIR240_HS.create () ; defs = STIR240_HS.create () }
  in
  let uses_defs_cfg : uses_defs CFG.t = CFG.map_data ~f:create_block_uses_defs cfg in
  let transfer (label : CFG.label) (live_out : STIR240_HS.t) =
    let block_uses_defs = CFG.get_data_exn ~label uses_defs_cfg in
    HS.diff live_out block_uses_defs.defs |> HS.union  block_uses_defs.uses
  in
  Dataflow.dataflow_analyze
    uses_defs_cfg
    ~dir:(Dataflow.BACKWARD)
    ~top:(STIR240_HS.create)
    ~meet:(HS.union)
    ~transfer
    ~v_boundary:(STIR240_HS.create)
    ~eq:(HS.equal)
;;

let live_info_to_program_cfg
    (quad_cfg : RWT.program CFG.t) (live_info_cfg : live_info CFG.t) : program CFG.t =
  let rec live_info_acc (basic_block : RWT.program) ~(live_out : STIR240_HS.t) (acc : program) =
    match basic_block with
    | [] -> acc
    | instr :: rest ->
      let empty_uses_defs _ : uses_defs = 
        { uses = STIR240_HS.create () ; defs = STIR240_HS.create () }
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
  let merge_fn ~label (basic_block : RWT.program) (live_info : live_info) : program =
    let _ : CFG.label = label in
    live_info_acc (List.rev basic_block) ~live_out:live_info.out_val []
  in
  CFG.merge_data_exn quad_cfg live_info_cfg ~f:merge_fn
;;

(* ------------------------------------- INTERFACE FUNCTION ------------------------------------- *)

let live_info_analysis (cfg : RWT.program CFG.t) : program CFG.t =
  live_info_data_flow cfg |> live_info_to_program_cfg cfg
;;
