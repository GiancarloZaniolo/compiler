(* Optimizing for tail recursion 
 * 
 * Checks all predecessors of EXIT for if their last instruction before returning is a recursive
 *  call *)

open Core 

module A = Assem
module QWT = Assem.Quad_With_Temps
module STIR = A.Stack_Temp_Imm_Reg
module Label = A.Label
module Label_HS = Label.Hash_set
module CFG = Cfg
module STIR_HT = STIR.Table
module Temp_HT = Temp.Table
module Temp_HS = Temp.Hash_set
module Edge = CFG.Edge
module Edge_HT = Edge.Table

let tail_recursion_optimize (cfg :  QWT.program CFG.t) : unit = 
  (* go to top block to find function name *)
  let fn_name_block = (match CFG.succs cfg Label.ENTRY_LABEL with
    | top :: [] -> top
    | _ -> failwith "Expected function to have a single first block") in
  let fn_name = (match fn_name_block with
    | Label.Fn_label f -> f
    | _ -> failwith "First line of function must be function label") in
  
  let tail_recurse_blocks = CFG.preds cfg Label.EXIT_LABEL in

  let find_if_candidate acc label = 
    let instrs = CFG.get_data_exn cfg ~label in 
    let rec check_last_three instrs acc = 
      (match instrs with
      | (QWT.Call c) :: _ :: QWT.Return _ :: [] -> 
        if Symbol.equal c.fn_label.name fn_name.name then 
          Some (label,c,acc)
        else
          None
      | instr :: rest -> check_last_three rest (instr :: acc)
      | [] -> None) in
      (match check_last_three instrs [] with
      | Some bl -> bl :: acc
      | None -> acc) in
  (* all tail-recursible blocks' data *)
  let blocks_t_rec = List.fold tail_recurse_blocks ~init:[] ~f:find_if_candidate in

  if List.length blocks_t_rec > 0 then
    (* Label of block to goto for tail recursive blocks *)
    let new_l = Local_label.create () in
    (* Data for new fn_lbl and its child block *)
    let (new_top_data,new_next_data) = (match CFG.get_data_exn cfg ~label:fn_name_block with
      | fn_lbl :: rest -> 
        ([fn_lbl ; QWT.Goto (Local_label new_l)], (QWT.Label (Local_label new_l)) :: rest)
      (* remove top block edges, insert edge to next, set next block out edges *)
      | _ -> failwith "expected more function label in top block") in
    (* Set edges and data of fn_label and child blocks *)
    CFG.set_data cfg ~label:fn_name_block ~data:new_top_data;
    CFG.set_data cfg ~label:(Local_label new_l) ~data:new_next_data;
    let transfer_edge e = 
      CFG.rem_succ cfg ~pred:fn_name_block ~succ:e;
      CFG.set_succ cfg ~pred:(Local_label new_l) ~succ:e in 
    List.iter (CFG.succs cfg fn_name_block) ~f:transfer_edge;
    CFG.set_succ cfg ~pred:(fn_name_block) ~succ:(Local_label new_l);
    (* Set edges and data of tail recursive blocks *)
    let set_new_bl_data ((label,call,acc) : CFG.label * Assem_intf.call * QWT.instr list)  =
      (* insert movs in function call *)
      let params_move = List.zip_exn call.fn_label.param_temps fn_name.param_temps in
      let add_mov_to_acc acc (src,dest) = 
        (QWT.Mov { src = STIR.Temp src ; dest = STIR.Temp dest }) :: acc in
      let acc0 = List.fold_left params_move ~init:acc ~f:add_mov_to_acc in
      let new_data = List.rev ((QWT.Goto (Local_label new_l)) :: acc0) in
      CFG.set_data cfg ~label ~data:new_data;
      (* CFG.rem_succ cfg ~pred:label ~succ:Label.EXIT_LABEL; *)
      CFG.set_succ cfg ~pred:label ~succ:(Local_label new_l) in
    List.iter blocks_t_rec ~f:set_new_bl_data
  else
    ()
