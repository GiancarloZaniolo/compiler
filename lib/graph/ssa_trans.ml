(* File containing code to translate a CFG to SSA, and to destroy SSA 
 * Implementation heavily inspired by "SSA-Based Compiler Design"
   
 * SSA translation cases on the structure of the instruction lists in basic blocks. There are some 
 *  invariants that must be preserved when dealing with ssa:
 * Invars:
 * - First line is a label
 * - All phi functions come immediately after the label
 * - If you change the CFG edges, you must fix:
 *  - The phi functions (each source has an associated parent block where it will be placed in 
        destruction)
    - The actualy labels in the jumps must match whatever the cfg edges are
 * - The last instruction must be either a ret or a jump (conditional or non-conditional)
 * - Maybe other stuff (we will find out) 
 *
 * Note: Default test cases only test the destruction behavior of tests directly generated by our
 *  front-end. Changing the cfg structure could expose bugs in this implementation.
 *)

open Core

module QWT = Assem.Quad_With_Temps
module CFG = Cfg
module VHT = CFG.Vertex.Table
module VHS = CFG.Vertex.Hash_set
module STIR = Assem.Stack_Temp_Imm_Reg
(* We need STIR instead of Temp has tables because we often use the table keys to insert 
   instructions *)
module STIR_HT = STIR.Table
module Temp_M = Temp.Map
module DT = Dominator_tree
module DF = Dominance_frontier
module A = Assem
module L = A.Label
module L_HT = L.Table
module L_HS = L.Hash_set


let insert_phi (cfg : QWT.program CFG.t) (r_dom_tree : DT.reverse_t ) : unit  = 
(* Algorithm found on page 27 of SSA-Based Compiler Design textbook *)

  let defs_ht = STIR_HT.create () in
  let iter_block ~label:vert ~data:instrs = 
    let insert_dest instr = 
      let op_opt = (match instr with
        | QWT.Binop b -> Some b.dest
        | QWT.Unop u -> Some u.dest
        | QWT.Mov m -> Some m.dest
        | QWT.Mem_read m -> Some m.dest
        | _ -> None) in (*does not care about phi, guaranteed to be another var*)
      (match op_opt with
      | Some ((STIR.Temp _) as op) -> 
        let op_def_set = STIR_HT.find_or_add defs_ht op ~default:VHS.create in
        Hash_set.add op_def_set vert
      | Some op ->
        sprintf "Expected destination to be a temp. Got `%s` instead" (STIR.format_operand op)
        |> failwith
      | None -> ()) in
    List.iter (instrs) ~f:insert_dest in
  CFG.iteri ~f:iter_block cfg;

  let dom_front = DF.compute cfg r_dom_tree in

  let for_one_op op = 
    (match op with
    | STIR.Temp _ ->
      let defs_op = STIR_HT.find_exn defs_ht op in
      let frontier = VHS.create () in
      let worklist = Hash_set.to_list defs_op in
      let rec while_w_not_empty w = 
        (match w with
        | x :: w_rem -> 
          (let for_one_y curr_w y = 
            if not (Hash_set.mem frontier y) then 
              ((match CFG.get_data_exn cfg ~label:y with
              | flabel :: lines -> 
                CFG.set_data cfg 
                  ~label:y 
                  ~data:(flabel::(QWT.Phi { dest = op ; srcs = STIR.Table.create ()})::lines)
              | _ -> ());
              Hash_set.add frontier y;
              (if not (Hash_set.mem defs_op y) then
                 y::curr_w
              else
                curr_w))
            else
              curr_w in
          let new_w = List.fold_left (DF.frontier_exn dom_front x) ~init:w_rem ~f:for_one_y in
          while_w_not_empty new_w)
        | [] -> ())
      in
      while_w_not_empty worklist
    | _ ->
      sprintf "Expected destination to be a temp. Got `%s` instead" (STIR.format_operand op)
      |> failwith)
  in 

  STIR_HT.iter_keys defs_ht ~f:for_one_op

let rename_vars (cfg: QWT.program CFG.t) (r_dom_tree : DT.reverse_t ) : unit = 

  (* TODO: Could alternatively do a hash set for this and move everything to an assoc set later *)
  let temp_map_ref = ref(Temp_M.empty) in
  (* Step 1: 1 pass, collect all of the relevant variable versions *)
  let rec find_orig_temps_blk (instrs : QWT.program) =
    (match instrs with
    | instr :: rest -> 
      let ops = (match instr with
        | QWT.Binop b -> [ b.dest ]
        | QWT.Unop u -> [ u.dest ]
        | QWT.Mov m -> [ m.dest ]
        | QWT.Mem_read m -> [ m.dest ]
        | QWT.Label (A.Label.Fn_label f) -> List.map f.param_temps ~f:(fun t -> STIR.Temp t) 
        | QWT.Call c -> (match c.dest with
          | Some dest -> [ STIR.Temp dest ]
          | None -> [])
        | _ -> []) in (* Phi dest is guaranteed to not originally exist in the program *)
      let fold_op_into_temp_map temp_map_acc op = 
        (match op with
        | STIR.Temp t -> Temp_M.set temp_map_acc ~key:t.temp ~data:t.temp 
        | (STIR.Arg_In_Stack_Idx _|STIR.Arg_Out_Stack_Idx _|STIR.Reg _|STIR.Imm32 _|STIR.Imm64 _
          | STIR.Addr_mode _) ->
          sprintf "Unexpected destination in quad pseudo-assembly: `%s`" (STIR.format_operand op)
          |> failwith)
      in
      temp_map_ref := List.fold ops ~f:(fold_op_into_temp_map) ~init:(!temp_map_ref) ;
      find_orig_temps_blk rest
    | [] -> ()) in
  CFG.iter cfg ~f:(find_orig_temps_blk); 

  (* TODO: Add an access function for forwards dominators and use that instead of manually 
       rebuilding it here *)
  (* Step 1.5, create the forwards dominator *)
  (* As of right now, none of the interface functions seem to allow you to access elements of the
     forward dominator tree *)
  let fwd_dom_tree = VHT.create () in
  let add_one_empty_vert ~label = VHT.add_exn fwd_dom_tree ~key:label ~data:(VHS.create ()) in
  CFG.iter_label cfg ~f:(add_one_empty_vert);
  let flip_dom_tree_one_label ~label:vert = 
    (match DT.idom_exn r_dom_tree ~node:vert with
    | Some dest -> (match VHT.find fwd_dom_tree dest with
      | Some dest_vert -> 
        Hash_set.add dest_vert vert
      | None -> 
        failwith "At this point all graph nodes should have a fwd_dom_tree node")
    | None -> ()) in
  CFG.iter_label cfg ~f:flip_dom_tree_one_label ;
  Hash_set.remove (VHT.find_exn fwd_dom_tree L.ENTRY_LABEL) L.ENTRY_LABEL;

  (* Step 2: actually assign everything *)
  (* There will be a dfs over the tree *)
  let visited_n_phi_ht = VHT.create () in
  let rec gen_phi_dfs temp_map vert = 
    (if VHT.mem visited_n_phi_ht vert then failwith "Forwards dominator tree should be a tree");
    let phi_dest_ht = STIR_HT.create () in
    VHT.add_exn visited_n_phi_ht ~key:vert ~data:phi_dest_ht;
    let rec fix_use op m = 
      (match op with
      | STIR.Temp t_op -> 
        (match Temp_M.find m t_op.temp with
        | Some t_curr -> STIR.Temp { temp = t_curr ; size = t_op.size }
        (* TODO: Since we remove dead instructions after SSA, we should make sure that the
           below case never occurs (failwith instead of returning op) *)
        | None -> op) (* This is legal because you can use non-defined temps after returns *)
      | (STIR.Imm32 _|STIR.Imm64 _) -> op
      | STIR.Addr_mode exp ->
        let base =
          match fix_use (STIR.Temp exp.base) m with
          | STIR.Temp t -> t
          | _ -> failwith "Expected to fix temp to temp"
        in
        let index =
          match fix_use (STIR.Temp exp.index) m with
          | STIR.Temp t -> t
          | _ -> failwith "Expected to fix temp to temp"
        in
        STIR.Addr_mode { exp with base ; index }
      | (STIR.Arg_In_Stack_Idx _|STIR.Arg_Out_Stack_Idx _|STIR.Reg _) -> 
        sprintf "Expected use to be a temporary register or immedtiate. Got `%s`"
          (STIR.format_operand op)
        |> failwith)
    in
    let fix_def op m = 
      (match op with
      | STIR.Temp t_op -> 
        let new_t = Temp.create () in
        (STIR.Temp { temp = new_t ; size = t_op.size }, 
        Temp_M.set m 
        (* Right now, we generate fresh temps even if it is the first occurence. DO NOT CHANGE *)
          ~key:t_op.temp
          ~data:new_t)
      | _ ->
        sprintf "Expected destination to be a temporary registers. Got `%s`"
          (STIR.format_operand op)
        |> failwith)
    in
    let fix_instr (acc,temp_map) instr =
      (match instr with
      | QWT.Binop b ->
        let lhs = fix_use b.lhs temp_map in
        let rhs = fix_use b.rhs temp_map in
        let (dest,temp_map') = fix_def b.dest temp_map in
        ((QWT.Binop { b with lhs ; rhs ; dest }) :: acc, temp_map')
      | QWT.Unop u -> 
        let src = fix_use u.src temp_map in 
        let (dest,temp_map') = fix_def u.dest temp_map in
        ((QWT.Unop { u with src ; dest}) :: acc, temp_map')
      | QWT.Mov m -> 
        let src = fix_use m.src temp_map in 
        let (dest,temp_map') = fix_def m.dest temp_map in
        ((QWT.Mov { src ; dest }) :: acc, temp_map')
      | QWT.Phi p ->
        let (dest,temp_map') = fix_def p.dest temp_map in
        STIR_HT.add_exn phi_dest_ht ~key:(STIR.resize_64 dest) ~data:(STIR.resize_64 p.dest) ; 
        ((QWT.Phi { p with dest}) :: acc, temp_map')
      | QWT.If i -> ((QWT.If
        { i with 
          lhs = fix_use i.lhs temp_map 
        ; rhs = fix_use i.rhs temp_map })
        :: acc, temp_map)
      | QWT.Mem_read m ->
        let src = fix_use m.src temp_map in
        let (dest,temp_map') = fix_def m.dest temp_map in
        ((QWT.Mem_read { src ; dest }) :: acc,temp_map')
      | QWT.Mem_write m -> ((QWT.Mem_write 
        { src = fix_use m.src temp_map 
        ; dest = fix_use m.dest temp_map })
        :: acc, temp_map)
      | Call c ->
        let fix_used_sized_temp st =
          (match fix_use (STIR.Temp st) temp_map with
          | STIR.Temp fixed_param -> fixed_param
          | stir ->
            sprintf "Expected to fix temp to a temp. Instead got `%s`" (STIR.format_operand stir)
            |> failwith)
        in
        let (dest', temp_map') =
          (match c.dest with
          | Some dest -> (match fix_def (STIR.Temp dest) temp_map with
            | (STIR.Temp fixed_dest, temp_map') -> (Some fixed_dest, temp_map')
            | (stir, _) ->
              sprintf "Expected to fix temp to a temp. Instead got `%s`" (STIR.format_operand stir)
              |> failwith)
          | None -> (None, temp_map))
        in
        let param_temps = List.map ~f:fix_used_sized_temp c.fn_label.param_temps in
        (QWT.Call { dest = dest' ; fn_label = { c.fn_label with param_temps} } :: acc, temp_map')
      | QWT.Label (A.Label.Fn_label f) ->
        let fix_def_sized_temp (fixed_param_temps_acc, temp_map_acc) st =
          (match fix_def (STIR.Temp st) temp_map_acc with
          | (STIR.Temp fixed_param, temp_map') -> (fixed_param :: fixed_param_temps_acc, temp_map')
          | (stir, _) ->
            sprintf "Expected to fix temp to a temp. Instead got `%s`" (STIR.format_operand stir)
            |> failwith)
        in
        let (param_temps_rev, temp_map') =
          List.fold ~f:fix_def_sized_temp ~init:([], temp_map) f.param_temps
        in
        let param_temps = List.rev param_temps_rev in
        (QWT.Label (A.Label.Fn_label { f with param_temps }) :: acc, temp_map')
      | QWT.Return ret_opnd_opt ->
        let ret_opnd_opt' = Option.map ~f:(fun o -> fix_use o temp_map) ret_opnd_opt in
        (QWT.Return ret_opnd_opt' :: acc, temp_map)
      | (Goto _|Label _|Directive _|Comment _) -> (instr :: acc, temp_map)) in
    let (rev_acc, temp_map_new) = 
        List.fold_left (CFG.get_data_exn cfg ~label:vert) ~init:([],temp_map) ~f:fix_instr in
    CFG.set_data cfg ~label:vert ~data:(List.rev rev_acc);
    (* NOTE: right now, I have the phi functions in 3-addr form, we could have had them as a map 
       associated with each basic block, but I just want to have working SSA at this point. Also,
       Having it as instructions means you do not have to separately manage phi functions, you can 
       handle them in optimizations as you would any other instruction *)
    
    let insert_successor_phi succ_vert = 
      let phi_dest_ht_optn = VHT.find visited_n_phi_ht succ_vert in
      let instrs_no_fn_label = (match CFG.get_data_exn cfg ~label:succ_vert with
      | _ :: instrs -> instrs
      | _ -> []) in
      let rec iter_phi_instrs instrs = 
        (match instrs with
        | (QWT.Phi p) :: rest -> 
          let phi_dest_t = (match phi_dest_ht_optn with
            | Some phi_dest_ht -> (match STIR_HT.find_exn phi_dest_ht p.dest with
              | STIR.Temp t -> t.temp
              | _ -> failwith "phi destination must be a temp")
            | None -> (match p.dest with 
              | STIR.Temp t -> t.temp
              | _ -> failwith "phi destination must be a temp")) in
          let new_phi_src_64 = Temp_M.find_exn temp_map_new phi_dest_t in
          (match p.dest with
          | STIR.Temp p_d -> 
            if Temp.equal phi_dest_t new_phi_src_64 then
              ()
            else
              (match STIR_HT.find p.srcs (STIR.Temp { temp =  new_phi_src_64 ; size = p_d.size }) with
              | Some nps64_p_srcs -> Hash_set.add nps64_p_srcs vert (*need to add vertex to assem intf*)
              | None -> 
                let new_nps64_src = L_HS.create () in
                Hash_set.add new_nps64_src vert;
                STIR_HT.add_exn p.srcs 
                  ~key:(STIR.Temp { temp =  new_phi_src_64 ; size = p_d.size }) ~data:new_nps64_src) ;
          | _ -> failwith "Phi functions should always be on temps");
          iter_phi_instrs rest
        | _ -> ()) in
      iter_phi_instrs instrs_no_fn_label in
    
      List.iter (CFG.succs cfg vert) ~f:insert_successor_phi;

    Hash_set.iter (VHT.find_exn fwd_dom_tree vert) ~f:(gen_phi_dfs temp_map_new) in
    
  gen_phi_dfs !temp_map_ref L.ENTRY_LABEL

let create_ssa (cfg : QWT.program CFG.t) : unit = 
  (* details in notes, sec 3.1 alg 3.1 *)
  let r_dom_t = DT.compute_reverse_dt cfg in
  insert_phi cfg (r_dom_t);
  rename_vars cfg (r_dom_t)


type parallel_copy = Append of QWT.instr list | B_Blocks of QWT.instr list VHT.t

let destroy_ssa (cfg : QWT.program CFG.t) : unit = 
  let p_copies : parallel_copy VHT.t = VHT.create () in
  let acc_p_copies_for_block child_bl = 
    let (fn_label, instrs) = (match CFG.get_data_exn cfg ~label:child_bl with
      | (QWT.Label fn_label) :: instrs -> (QWT.Label fn_label, instrs)
      (* TODO: replace comment with noop *)
      | edge_case -> (QWT.Comment "Replace this with noop",edge_case)) in
    let rec acc_phi_instrs instrs = 
      (match instrs with
      | (QWT.Phi p) :: rest -> 
        let one_phi_src_parent src_temp parent_bl = 
          (match VHT.find p_copies parent_bl with
            | Some Append acc -> 
              VHT.set p_copies 
                ~key:parent_bl 
                ~data:(Append ((QWT.Mov { src = src_temp ; dest = p.dest }) :: acc))
            | Some B_Blocks to_parent_ht -> 
              let curr_bl_acc = (match VHT.find to_parent_ht child_bl with 
                | Some acc -> acc
                | None -> [QWT.Goto child_bl]) in
              VHT.set to_parent_ht ~key:child_bl ~data:((QWT.Mov { src = src_temp ; dest = p.dest}) :: curr_bl_acc)
            | None -> 
              if Int.(<=) (List.length (CFG.succs cfg parent_bl)) 1 then
                VHT.set p_copies ~key:parent_bl ~data:(Append [QWT.Mov { src = src_temp ; dest = p.dest }])
              else
                let to_parent_ht = VHT.create () in
                VHT.add_exn  
                to_parent_ht 
                  ~key:child_bl 
                  ~data:[QWT.Mov { src = src_temp ; dest = p.dest } ; QWT.Goto child_bl];
                VHT.add_exn p_copies ~key:parent_bl ~data:(B_Blocks to_parent_ht)) in
        let one_phi_src ~key:src_temp ~data:parent_bl_s = 
          Hash_set.iter parent_bl_s ~f:(fun parent_bl -> one_phi_src_parent src_temp parent_bl) in
        STIR_HT.iteri p.srcs ~f:one_phi_src;
        acc_phi_instrs rest
      | rest -> rest) in
    let philess_instrs = acc_phi_instrs instrs in
    CFG.set_data cfg ~label:child_bl ~data:(fn_label :: philess_instrs) in

  (* Note: Cannot use CFG.iteri, mutation is not allowd during iteration *)
  List.iter (CFG.get_all_labels cfg) ~f:acc_p_copies_for_block;

  let insert_p_copies_for_block ~key:label ~data:p_copy =
    (match p_copy with
    | Append a -> 
      let rec get_bottom_elem = function
        | bottom :: [] -> ([],bottom)
        | instr :: instrs -> let (instrs_no_b, bottom) = get_bottom_elem instrs in
          (instr :: instrs_no_b, bottom)
        | [] -> failwith "basic block should never be empty" in
      let (curr_instrs,jump) = get_bottom_elem (CFG.get_data_exn cfg ~label) in
      CFG.set_data cfg ~label ~data:(curr_instrs @ (a @ [jump]))
    | B_Blocks b -> 
      let parent_new_label_map = L_HT.create () in
      let one_new_bb ~key:child_label ~data:instrs = 
        let new_b_label = L.Local_label (Local_label.create ()) in
        CFG.set_succ cfg ~pred:label ~succ:new_b_label;
        CFG.set_succ cfg ~pred:new_b_label ~succ:child_label;
        CFG.rem_succ cfg ~pred:label ~succ:child_label;
        CFG.set_data cfg ~label:new_b_label ~data:((QWT.Label new_b_label)::instrs);
        let child_label_instr = (match child_label with
          | L.Local_label _ -> child_label
          | _ -> failwith "Child node should always have a regular label") in
        L_HT.add_exn parent_new_label_map ~key:child_label_instr ~data:new_b_label in

      VHT.iteri b ~f:one_new_bb;

      let rec remap_labels instrs =
        (match instrs with
        | instr :: rest -> 
          (match instr with
          | QWT.Goto g -> (match L_HT.find parent_new_label_map g with
            | Some l -> (QWT.Goto l) :: (remap_labels rest)
            | None -> instr :: (remap_labels rest))
          | QWT.If i ->
            let if_true = (match L_HT.find parent_new_label_map i.if_true with
              | Some l -> l
              | None -> i.if_true) in
            let if_false = (match L_HT.find parent_new_label_map i.if_false with
              | Some l -> l
              | None -> i.if_false) in
            (QWT.If { i with if_true ; if_false }) :: (remap_labels rest)
          | _ -> instr :: (remap_labels rest))
        | [] -> []) in
        let curr_instrs = CFG.get_data_exn cfg ~label in 

        CFG.set_data cfg ~label ~data:(remap_labels curr_instrs)) in

  VHT.iteri p_copies ~f:insert_p_copies_for_block