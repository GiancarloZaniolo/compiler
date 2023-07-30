(* Module for translating quad assembly to control-flow graphs and back *)

open Core

module AS = Assem
module AL = Assem.Label
module QWT = AS.Quad_With_Temps
module CFG = Cfg
module VHT = CFG.Vertex.Table
module VHS = CFG.Vertex.Hash_set

let quad_to_cfg (quad : QWT.program) : QWT.program CFG.t list =
  let rec quad_to_cfg_rec
      (remaining : QWT.program) (acc : QWT.program CFG.t list)
      (cur_block : QWT.program) (cur_g : QWT.program CFG.t) (cur_label_opt : CFG.label option) 
      : QWT.program CFG.t list =
    let set_succs_and_block (succs : CFG.label list) (block) (label : CFG.label) : unit =
      List.iter ~f:(fun succ ->
        (* In some cases where loops do not terminate (while(true)), the generated IR does not
           generate a conditional jump. This can disconnect ENTRY_LABEL from EXIT_LABEL. To avoid
           this we could say that EXIT_LABEL is a successor to any loop. However, we don't have loop
           detection so we conservatively say that any block that jumps back to a block we have
           already seen can EXIT_LABEL (assuming that loop headers always appear before their bodies
           in the generated IR). *)
        (if CFG.mem_label cur_g succ then
          match succ with
          | AL.MEM_LABEL | AL.ARITH_LABEL -> ()
          | _ -> CFG.set_succ cur_g ~pred:label ~succ:AL.EXIT_LABEL);
        CFG.set_succ cur_g ~pred:label ~succ) succs ;
      CFG.set_data cur_g ~label ~data:(List.rev block)
    in
    match remaining with
    | [] ->
      Option.iter ~f:(set_succs_and_block [AL.EXIT_LABEL] cur_block) cur_label_opt ;
      cur_g :: acc
    | (QWT.Label (AL.Fn_label fn_label) as fn) :: remaining' ->
      Option.iter ~f:(set_succs_and_block [AL.EXIT_LABEL] cur_block) cur_label_opt ;
      let new_label = AL.Fn_label fn_label in
      let fn_cfg_init _ : QWT.program CFG.t =
        let new_g = CFG.create fn_label in
        CFG.set_succ new_g ~pred:AL.ENTRY_LABEL ~succ:new_label ;
        CFG.set_data new_g ~label:AL.ENTRY_LABEL ~data:[] ;
        CFG.set_data new_g ~label:AL.EXIT_LABEL ~data:[] ;
        CFG.set_succ new_g ~pred:AL.ARITH_LABEL ~succ:AL.EXIT_LABEL ;
        CFG.set_data new_g ~label:AL.ARITH_LABEL ~data:[] ;
        CFG.set_succ new_g ~pred:AL.MEM_LABEL ~succ:AL.EXIT_LABEL ;
        CFG.set_data new_g ~label:AL.MEM_LABEL ~data:[] ;
        new_g
      in
      let new_g = fn_cfg_init () in
      let acc' = cur_g :: acc in
      let new_block = [fn] in
      quad_to_cfg_rec remaining' acc' new_block new_g (Some new_label)
    | ((QWT.Goto succ) as goto_instr) :: ((QWT.Label new_qwt_label) as label_instr) :: remaining' ->
      let cur_block' = goto_instr :: cur_block in
      Option.iter ~f:(set_succs_and_block [succ] cur_block') cur_label_opt ;
      let new_label = Some new_qwt_label in
      let new_block = [label_instr] in
      quad_to_cfg_rec remaining' acc new_block cur_g new_label
    | [ QWT.Goto _ ] -> failwith "Expected a label after Goto. Got end of program instead."
    | QWT.Goto _ :: instr :: _ ->
      sprintf "Expected a label after Goto. Got `%s` instead." (QWT.format instr) |> failwith
    | ((QWT.If cond_jmp) as if_instr) :: ((QWT.Label new_qwt_label) as label_instr) :: remaining' ->
      let succ_true = cond_jmp.if_true in
      let succ_false = cond_jmp.if_false in
      let cur_block' = if_instr :: cur_block in
      Option.iter ~f:(set_succs_and_block [ succ_true ; succ_false ] cur_block') cur_label_opt ;
      let new_label = Some new_qwt_label in
      let new_block = [label_instr] in
      quad_to_cfg_rec remaining' acc new_block cur_g new_label
    | [ QWT.If _ ] -> failwith "Expected a label after Goto. Got end of program instead."
    | QWT.If _ :: instr :: _ ->
      sprintf "Expected a label after conditional jump. Got `%s` instead."
        (QWT.format instr)
      |> failwith
    | Return _ as ret_instr :: remaining' ->
      let cur_block' = ret_instr :: cur_block in
      Option.iter ~f:(set_succs_and_block [AL.EXIT_LABEL] cur_block') cur_label_opt;
      let new_label_opt = None in
      let new_block = [] in
      quad_to_cfg_rec remaining' acc new_block cur_g new_label_opt
    | (QWT.Label qwt_label) as instr :: remaining' ->
      (match cur_label_opt with
      | None ->
        let new_block = [instr] in
        let new_label = Some qwt_label in
        quad_to_cfg_rec remaining' acc new_block cur_g new_label 
      | Some _ -> sprintf "Unexpected label: %s" (QWT.format instr) |> failwith)
    | (QWT.Unop _|QWT.Mov _|QWT.Call _|QWT.Mem_read _|QWT.Mem_write _|QWT.Directive _|QWT.Comment _
      |QWT.Binop _)
      as instr :: remaining' ->
      (match cur_label_opt with
      | None -> quad_to_cfg_rec remaining' acc cur_block cur_g cur_label_opt
      | Some _ -> quad_to_cfg_rec remaining' acc (instr :: cur_block) cur_g cur_label_opt)
    | (QWT.Phi _) :: _ -> failwith "Phi functions should only exist in CFG, never before translation"

  in
  let empty_fn_label : AL.fn_label = { name = Symbol.symbol "" ; param_temps = [] ; ret_size_opt = None} in
  let result_extra_empty_at_end = quad_to_cfg_rec quad [] [] (CFG.create empty_fn_label ) None in
  let cfgs =
    List.sub ~pos:0 ~len:((List.length result_extra_empty_at_end) - 1) result_extra_empty_at_end
  in
  List.iter cfgs ~f:(CFG.remove_unreachable_nodes) ;
  cfgs

(* TODO: double check, is this even real dfs? *)
let list_cfg_to_list (cfg : 'a list CFG.t) : 'a list =  
  (* TODO: could try to optimize order of cfg blocks, for now, just insert in DFS order
     (which is not necessarily the same as the original pseudo-assembly, but is equivalent) *)
  (* TODO: in what order are if statement blocks inserted? should I reverse mine or you reverse upon
     insertion? *)
  let visited = VHS.create () in 
  let stack = Stack.create () in
  Hash_set.add visited AL.ENTRY_LABEL ;
  Stack.push stack AL.ENTRY_LABEL;
  (* Reverse accumulator *)
  let rec acc_program acc = 
    let push_if_not_vted v = 
      (match Hash_set.strict_add visited v with 
      | Ok () -> Stack.push stack v 
      | Error _ -> () ) in
    match Stack.pop stack with
    | Some AL.EXIT_LABEL -> acc_program acc
    | Some AL.ENTRY_LABEL -> 
      List.iter (CFG.succs cfg AL.ENTRY_LABEL) ~f:push_if_not_vted ;
      acc_program acc
    | Some vert -> 
      List.iter (CFG.succs cfg vert) ~f:push_if_not_vted;
      acc_program (List.rev_append (CFG.get_data_exn cfg ~label:vert) acc)
    | None -> acc
  in
  List.rev (acc_program [])

let list_cfg_program_to_list (cfgs : 'a list CFG.program) : 'a list =
  List.concat_map ~f:list_cfg_to_list cfgs

let%expect_test "Test idempotency of CFG translation" =
  let source_filename = "/autograder/dist/tests/l2-basic/for01.l2" in
  let (tst, ctxts) =
    Parse.parse ~source_filename ~header_filename:None
    |> Elaborate.elaborate |> Typechecker.typecheck
  in
  let irt = ctxts |> Ir_trans.translate tst in
  let program1 = Three_addr_trans.codegen irt false false in
  let cfg = program1 |> quad_to_cfg in
  let program2 = cfg |> List.concat_map ~f:list_cfg_to_list in
  let program1_str = Print_utils.pp_list ~sep:"\n" ~f:QWT.format program1 in
  let program2_str = Print_utils.pp_list ~sep:"\n" ~f:QWT.format program2 in
  sprintf "Before trans:\n%s\n--------------\nAfter trans:\n%s"
    program1_str
    program2_str
  |> prerr_endline ;
  [%expect{|
    Before trans:
    _c0_main():
    	%t3_S_32 <-- (32):$254
    	%t4_S_32 <-- (32):$1
    	%t5_S_32 <-- (32):$0
    	goto .L1
    .L1
    	%t10_S_32 <-- %t3_S_32
    	%t11_S_32 <-- (32):$0
    	if (%t10_S_32 > %t11_S_32) .L2 .L3
    .L2
    	%t12_S_32 <-- %t3_S_32
    	%t13_S_32 <-- (32):$2
    	S_32_RAX <-- %t12_S_32
    	S_32_RDX <-- CDQ S_32_RAX
    	S_32_RDX <-- S_32_RAX % %t13_S_32
    	%t7_S_32 <-- S_32_RDX
    	%t14_S_32 <-- %t7_S_32
    	%t15_S_32 <-- (32):$0
    	if (%t14_S_32 == %t15_S_32) .L4 .L5
    .L4
    	%t6_S_32 <-- (32):$0
    	goto .L6
    .L5
    	%t6_S_32 <-- (32):$1
    	goto .L6
    .L6
    	%t16_S_32 <-- %t4_S_32
    	%t17_S_32 <-- (32):$0
    	if (%t16_S_32 < %t17_S_32) .L7 .L8
    .L7
    	%t18_S_32 <-- (32):$1
    	%t19_S_32 <-- (32):$0
    	S_32_RAX <-- %t18_S_32
    	S_32_RDX <-- CDQ S_32_RAX
    	S_32_RAX <-- S_32_RAX / %t19_S_32
    	%t8_S_32 <-- S_32_RAX
    	S_32_RAX <-- %t8_S_32
    	ret
    	goto .L9
    .L8
    	goto .L9
    .L9
    	%t20_S_32 <-- %t6_S_32
    	%t21_S_32 <-- (32):$1
    	if (%t20_S_32 == %t21_S_32) .L11 .L10
    .L10
    	%t22_S_32 <-- %t4_S_32
    	%t23_S_32 <-- (32):$10
    	%t4_S_32 <-- %t22_S_32 * %t23_S_32
    	goto .L12
    .L11
    	%t24_S_32 <-- %t4_S_32
    	%t25_S_32 <-- %t5_S_32
    	%t5_S_32 <-- %t24_S_32 + %t25_S_32
    	%t26_S_32 <-- %t4_S_32
    	%t27_S_32 <-- (32):$10
    	%t4_S_32 <-- %t26_S_32 * %t27_S_32
    	goto .L12
    .L12
    	%t28_S_32 <-- %t3_S_32
    	%t29_S_32 <-- (32):$2
    	S_32_RAX <-- %t28_S_32
    	S_32_RDX <-- CDQ S_32_RAX
    	S_32_RAX <-- S_32_RAX / %t29_S_32
    	%t9_S_32 <-- S_32_RAX
    	%t3_S_32 <-- %t9_S_32
    	goto .L1
    .L3
    	S_32_RAX <-- %t5_S_32
    	ret
    --------------
    After trans:
    _c0_main():
    	%t3_S_32 <-- (32):$254
    	%t4_S_32 <-- (32):$1
    	%t5_S_32 <-- (32):$0
    	goto .L1
    .L1
    	%t10_S_32 <-- %t3_S_32
    	%t11_S_32 <-- (32):$0
    	if (%t10_S_32 > %t11_S_32) .L2 .L3
    .L2
    	%t12_S_32 <-- %t3_S_32
    	%t13_S_32 <-- (32):$2
    	S_32_RAX <-- %t12_S_32
    	S_32_RDX <-- CDQ S_32_RAX
    	S_32_RDX <-- S_32_RAX % %t13_S_32
    	%t7_S_32 <-- S_32_RDX
    	%t14_S_32 <-- %t7_S_32
    	%t15_S_32 <-- (32):$0
    	if (%t14_S_32 == %t15_S_32) .L4 .L5
    .L4
    	%t6_S_32 <-- (32):$0
    	goto .L6
    .L6
    	%t16_S_32 <-- %t4_S_32
    	%t17_S_32 <-- (32):$0
    	if (%t16_S_32 < %t17_S_32) .L7 .L8
    .L8
    	goto .L9
    .L9
    	%t20_S_32 <-- %t6_S_32
    	%t21_S_32 <-- (32):$1
    	if (%t20_S_32 == %t21_S_32) .L11 .L10
    .L10
    	%t22_S_32 <-- %t4_S_32
    	%t23_S_32 <-- (32):$10
    	%t4_S_32 <-- %t22_S_32 * %t23_S_32
    	goto .L12
    .L12
    	%t28_S_32 <-- %t3_S_32
    	%t29_S_32 <-- (32):$2
    	S_32_RAX <-- %t28_S_32
    	S_32_RDX <-- CDQ S_32_RAX
    	S_32_RAX <-- S_32_RAX / %t29_S_32
    	%t9_S_32 <-- S_32_RAX
    	%t3_S_32 <-- %t9_S_32
    	goto .L1
    .L11
    	%t24_S_32 <-- %t4_S_32
    	%t25_S_32 <-- %t5_S_32
    	%t5_S_32 <-- %t24_S_32 + %t25_S_32
    	%t26_S_32 <-- %t4_S_32
    	%t27_S_32 <-- (32):$10
    	%t4_S_32 <-- %t26_S_32 * %t27_S_32
    	goto .L12
    .L7
    	%t18_S_32 <-- (32):$1
    	%t19_S_32 <-- (32):$0
    	S_32_RAX <-- %t18_S_32
    	S_32_RDX <-- CDQ S_32_RAX
    	S_32_RAX <-- S_32_RAX / %t19_S_32
    	%t8_S_32 <-- S_32_RAX
    	S_32_RAX <-- %t8_S_32
    	ret
    .L5
    	%t6_S_32 <-- (32):$1
    	goto .L6
    .L3
    	S_32_RAX <-- %t5_S_32
    	ret |}]
;;



