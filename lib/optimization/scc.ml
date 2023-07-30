(* Module which implementes Sparse Conditional Copy Propagation optimization, as described in:
 *  "Constant Propagation with Conditional Branches" Mark N. Wegman, F. Kenneth Zadeck
 *
 * Note:
 * This transformation makes a whole new cfg, old cfg is outdated by end
 *)



 (* Implementation notes: some deviations from paper algorithm: *)
   (* My version will operate on basic blocks instead of lines for cfg worklist *)
   (* My version will not have every use of a temp as a separate vertex cell *)
   (* Size 64 is not worth propagating on, can be fully optimized in peephole *)
   (* Registers cannot be included in our analysis *)
   (* Assem unop cannot be included in our analysis *)

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


type lattice_val = TOP | BOTTOM | CONST32 of int32 | CONST64 of int64 [@@deriving equal]
(* For debugging: *)
(* let format_lat_val thirty = (match thirty with
| CONST c -> sprintf "CONST %s" (Int32.to_string c)
| TOP -> "TOP"
| BOTTOM ->"BOTTOM") *)

type worklist_elem = Flow of Label.t * Label.t  | SSA of QWT.instr * Label.t

let scc_optimize (cfg :  QWT.program CFG.t) : QWT.program CFG.t = 
(* Helper: ============================================================== *)

  (* NOTE: assumes no division by 0 *)
  let precalc_binop_arith32 op lhs rhs = 
    (match op with
    | A.Add -> Int32.(+) lhs rhs
    | A.Sub -> Int32.(-) lhs rhs
    | A.Mul -> Int32.( * ) lhs rhs
    | A.Div -> Int32.(lhs / rhs)
    | A.Mod -> Int32.(rem lhs rhs)
    | A.LShift -> Int32.(lsl) lhs (Int32.to_int_exn rhs)
    | A.RShift -> Int32.(asr) lhs (Int32.to_int_exn rhs)
    | A.RShift_unsigned -> Int32.(lsr) lhs (Int32.to_int_exn rhs)
    | A.BWXor -> Int32.(lxor) lhs rhs
    | A.BWAnd -> Int32.(land) lhs rhs
    | A.BWOr -> Int32.(lor) lhs rhs) in

  let precalc_binop_arith64 op lhs rhs = 
    (match op with
    | A.Add -> Int64.(+) lhs rhs
    | A.Sub -> Int64.(-) lhs rhs
    | A.Mul -> Int64.( * ) lhs rhs
    | A.Div -> Int64.(lhs / rhs)
    | A.Mod -> Int64.(rem lhs rhs)
    | A.LShift -> Int64.(lsl) lhs (Int64.to_int_exn rhs)
    | A.RShift -> Int64.(asr) lhs (Int64.to_int_exn rhs)
    | A.RShift_unsigned -> Int64.(lsr) lhs (Int64.to_int_exn rhs)
    | A.BWXor -> Int64.(lxor) lhs rhs
    | A.BWAnd -> Int64.(land) lhs rhs
    | A.BWOr -> Int64.(lor) lhs rhs) in

  let precalc_binop_comp32 = function 
    | A.LessThan -> Int32.(<)
    | A.LessThanEq -> Int32.(<=)
    | A.GreaterThan -> Int32.(>)
    | A.GreaterThanEq -> Int32.(>=)
    | A.EqualsTo -> Int32.equal
    | A.NotEqualsTo -> (fun lhs rhs -> not (Int32.equal lhs rhs)) in

  let precalc_binop_comp64 = function 
    | A.LessThan -> Int64.(<)
    | A.LessThanEq -> Int64.(<=)
    | A.GreaterThan -> Int64.(>)
    | A.GreaterThanEq -> Int64.(>=)
    | A.EqualsTo -> Int64.equal
    | A.NotEqualsTo -> (fun lhs rhs -> not (Int64.equal lhs rhs)) in
    
(* Initialize: ========================================================== *)
  let worklist = Queue.create () in
  let temp_lat_ht = Temp_HT.create () in
  let edge_execable = Edge_HT.create () in
  let ssa_gr = Temp_HT.create () in
  let visited = Label_HS.create () in
  
  let add_all_edge_unvted_init ~label:src = 
    let succs = CFG.succs cfg src in
    List.iter succs ~f:(fun dest -> Edge_HT.add_exn edge_execable ~key:(src,dest) ~data:false)
  in
  CFG.iter_label cfg ~f:add_all_edge_unvted_init ;

  let set_t_default = function (* Anything used must be defined *)
    | QWT.Binop b -> (match b.dest with
      | STIR.Temp t -> Temp_HT.add_exn temp_lat_ht ~key:t.temp ~data:TOP
      | _ -> failwith "Destination should always be a temp")
    | QWT.Unop u -> (match u.dest with
      | STIR.Temp t -> Temp_HT.add_exn temp_lat_ht ~key:t.temp ~data:BOTTOM
      | _ -> failwith "Destination should always be a temp") 
      (* If calculated in advance, unops will cause incorrect behavior *)
    | QWT.Mov m -> (match m.dest with
      | STIR.Temp t -> Temp_HT.add_exn temp_lat_ht ~key:t.temp ~data:TOP
      | _ -> failwith "Destination should always be a temp")
    | QWT.Phi p -> (match p.dest with
      | STIR.Temp t -> Temp_HT.add_exn temp_lat_ht ~key:t.temp ~data:TOP
      | _ -> failwith "Destination should always be a temp")
    | QWT.Mem_read m -> (match m.dest with
      | STIR.Temp t -> Temp_HT.add_exn temp_lat_ht ~key:t.temp ~data:BOTTOM
      | _ -> failwith "Destination should always be a temp")
    | QWT.Label (Fn_label f) -> 
      List.iter f.param_temps ~f:(fun t -> Temp_HT.add_exn temp_lat_ht ~key:t.temp ~data:BOTTOM)
    | QWT.Call c -> (* Function call result cannot be cased on *)
      (match c.dest with
      | Some dest -> Temp_HT.add_exn temp_lat_ht ~key:dest.temp ~data:BOTTOM
      | None -> ())
    | QWT.Label _ | QWT.If _ | QWT.Goto _ | QWT.Return _ | QWT.Mem_write _ | QWT.Directive _ 
    | QWT.Comment _ -> () in
  CFG.iter cfg ~f:(fun f -> List.iter f  ~f:set_t_default);
  
  let succs_edge_l src = 
    let dest_l = CFG.succs cfg src in
    List.map dest_l ~f:(fun dest -> Flow (src,dest)) in
  Queue.enqueue_all worklist (succs_edge_l Label.ENTRY_LABEL);
  Hash_set.add visited Label.ENTRY_LABEL;

  (* Create all ssa edges *)
  let add_def temp = 
    (match Temp_HT.add ssa_gr ~key:temp ~data:[] with
    | `Duplicate | `Ok -> ()) in
  let add_use temp use_l = 
    (match Temp_HT.find ssa_gr temp with
    | Some dest_l -> Temp_HT.set ssa_gr ~key:temp ~data:(use_l :: dest_l)
    | None -> Temp_HT.add_exn ssa_gr ~key:temp ~data:[use_l]) in
  let rec add_ssa_edges node = function
  | instr :: rest -> (match instr with
    | QWT.Binop b -> 
      let l_temp = 
        (match b.lhs with
        | STIR.Temp t -> add_use t.temp (instr,node); Some (t.temp)
        | _ -> None) in
      (match b.rhs with
      | STIR.Temp t -> 
        if not (Option.equal Temp.equal l_temp (Some t.temp)) then
          add_use t.temp (instr,node)
      | _ -> ());
      (match b.dest with
      | STIR.Temp t -> add_def t.temp
      | _ -> ())
    | QWT.Unop u ->  
      (match u.src with | STIR.Temp t -> add_use t.temp (instr,node) | _ -> ()); 
      (match u.dest with | STIR.Temp t -> add_def t.temp | _ -> ())
    | QWT.Mov m -> 
      (match m.src with | STIR.Temp t -> add_use t.temp (instr,node) | _ -> ());
      (match m.dest with | STIR.Temp t -> add_def t.temp | _ -> ())
    | QWT.Phi p  -> 
      let for_one_phi_src temp = 
        (match temp with
        | STIR.Temp t -> 
            add_use t.temp (instr,node)
        | _ -> ());
       in
      STIR_HT.iter_keys p.srcs ~f:for_one_phi_src;
      (match p.dest with | STIR.Temp t -> add_def t.temp | _ -> ())
    | QWT.Mem_write m -> 
      let l_temp = (match m.src with
      | STIR.Temp t -> add_use t.temp (instr,node); Some (t.temp)
      | _ -> None) in
      (match m.dest with
      | STIR.Temp t -> 
        if not (Option.equal Temp.equal l_temp (Some t.temp)) then
          add_use t.temp (instr,node)
      | _ -> ())
    | QWT.If i -> 
      (match i.lhs with | STIR.Temp t -> add_use t.temp (instr,node) | _ -> ());
      (match i.rhs with | STIR.Temp t -> add_use t.temp (instr,node) | _ -> ())
    | QWT.Call _| QWT.Goto _| QWT.Label _ | QWT.Return _ | QWT.Mem_read _ | QWT.Comment _ 
    | QWT.Directive _ -> ()); (* No temps used in any other instructions *)
    add_ssa_edges node rest
  | [] -> () in
  List.iter (CFG.reverse_postorder_forward cfg) 
    ~f:(fun node -> add_ssa_edges node (CFG.get_data_exn cfg ~label:node));

(* End Initialize: ============================================================= *)

  let visit_phi phi instr_node = 
    (match phi with 
    | QWT.Phi p -> 
      let dest_temp = (match p.dest with
        | STIR.Temp t -> t.temp
        | _ -> failwith "Phi destination should always be a temp") in
      let fold_fn ~key:src_stir ~data:src_set acc = 
        let src_lat = (match src_stir with 
        | STIR.Temp t -> Temp_HT.find_exn temp_lat_ht t.temp
        | STIR.Imm32 c -> CONST32 c
        | STIR.Imm64 c -> CONST64 c
        | _ -> failwith "expected temp or immediate in phi function") in
        let one_src acc src = 
          if Edge_HT.find_exn edge_execable (src,instr_node) then
            (match acc with
            | BOTTOM -> BOTTOM
            | TOP -> src_lat
            | CONST32 c -> (match src_lat with
              | BOTTOM -> BOTTOM
              | TOP -> CONST32 c
              | CONST32 c2 -> if Int32.equal c c2 then CONST32 c else BOTTOM
              | CONST64 _ -> failwith "Different sized operands should never be in phi srcs")
            | CONST64 c -> (match src_lat with
              | BOTTOM -> BOTTOM
              | TOP -> CONST64 c
              | CONST32 _ -> failwith "Different size operand should never be in phi srcs"
              | CONST64 c2 -> if Int64.equal c c2 then CONST64 c else BOTTOM))
          else
            acc in 
          Hash_set.fold src_set ~init:acc ~f:one_src in
      let fold_res = STIR_HT.fold p.srcs ~init:TOP ~f:fold_fn in
      if equal_lattice_val (Temp_HT.find_exn temp_lat_ht dest_temp) fold_res then
        ()
      else
        (Temp_HT.set temp_lat_ht ~key:dest_temp ~data:fold_res;
        List.iter (Temp_HT.find_exn ssa_gr dest_temp) 
          ~f:(fun (instr,node) -> Queue.enqueue worklist (SSA (instr,node))))
    | _ -> failwith "Expected phi function in visit_phi") in

  let rec visit_phi_list instrs instrs_node =
    (match instrs with
    | QWT.Phi p :: rest -> 
      visit_phi (QWT.Phi p) instrs_node;
      visit_phi_list rest instrs_node
    | rest -> rest) in

  let visit_expression instr node = 
    let stir_to_lat_val = function
      | STIR.Imm32 c -> CONST32 c
      | STIR.Imm64 c -> CONST64 c
      | STIR.Temp t -> Temp_HT.find_exn temp_lat_ht t.temp
      | _ -> BOTTOM in
    let check_dest_same dest instr_lat_val = 
      (match dest with
        | STIR.Temp t -> 
          if equal_lattice_val (Temp_HT.find_exn temp_lat_ht t.temp) instr_lat_val then
            ()
          else
            Temp_HT.set temp_lat_ht ~key:t.temp ~data:instr_lat_val;
            List.iter (Temp_HT.find_exn ssa_gr t.temp)
              ~f:(fun (instr,node) -> Queue.enqueue worklist (SSA (instr,node)))
      | _ -> ()) in
    (match instr with
    | QWT.Binop b -> 
      let instr_lat_val = (match (stir_to_lat_val b.lhs, stir_to_lat_val b.rhs) with
      | (CONST32 lhs, CONST32 rhs) -> (match b.op with
        | A.Add | A.Sub | A.Mul | A.LShift | A.RShift | A.RShift_unsigned | A.BWXor | A.BWAnd 
        | A.BWOr -> CONST32 (precalc_binop_arith32 b.op lhs rhs)
        | A.Div | A.Mod -> 
          if (Int32.equal rhs Int32.zero)  
            || (Int32.(lhs = Int32.min_value) && Int32.(rhs = minus_one)) then
          BOTTOM
        else
          CONST32 (precalc_binop_arith32 b.op lhs rhs))
      | (CONST64 lhs, CONST64 rhs) -> (match b.op with
      | A.Add | A.Sub | A.Mul | A.LShift | A.RShift | A.RShift_unsigned | A.BWXor | A.BWAnd 
      | A.BWOr -> CONST64 (precalc_binop_arith64 b.op lhs rhs)
      | A.Div | A.Mod -> 
        if (Int64.equal rhs Int64.zero)  
          || (Int64.(lhs = Int64.min_value) && Int64.(rhs = minus_one)) then
        BOTTOM
      else
        CONST64 (precalc_binop_arith64 b.op lhs rhs))
      | (BOTTOM,_) | (_,BOTTOM) -> BOTTOM
      | _ -> TOP) in 
      check_dest_same b.dest instr_lat_val
    | QWT.Unop _ -> () (* Unop results initially set to bottom *)
    | QWT.Mov m -> 
      (match m.src with
      | STIR.Temp t_src ->
         check_dest_same m.dest (Temp_HT.find_exn temp_lat_ht t_src.temp)
      | STIR.Imm32 c -> 
        check_dest_same m.dest (CONST32 c)
      | STIR.Imm64 c -> 
        check_dest_same m.dest (CONST64 c)
      | _ ->  check_dest_same m.dest BOTTOM)
    | QWT.Phi _ -> visit_phi instr node
    | QWT.If i -> 
      if Hash_set.mem visited node then
        (match (stir_to_lat_val i.lhs, stir_to_lat_val i.rhs) with
        | (CONST32 lhs, CONST32 rhs) -> 
          if precalc_binop_comp32 i.op lhs rhs then
            Queue.enqueue worklist (Flow (node,i.if_true))    
          else
            Queue.enqueue worklist (Flow (node,i.if_false))    
        | (CONST64 lhs, CONST64 rhs) -> 
          if precalc_binop_comp64 i.op lhs rhs then
            Queue.enqueue worklist (Flow (node,i.if_true))    
          else
            Queue.enqueue worklist (Flow (node,i.if_false))   
        | (BOTTOM,_) | (_,BOTTOM) -> 
          Queue.enqueue worklist (Flow (node, i.if_true));
          Queue.enqueue worklist (Flow (node, i.if_false))
        | _ -> ()) 
    | _ -> ()) in
  
  let rec one_iter () = 
    (match Queue.dequeue worklist with
    | Some Flow (src,dest) -> 
      let edge = (src,dest) in
      if not(Edge_HT.find_exn edge_execable edge) then
        (Hash_set.add visited dest;
        Edge_HT.set edge_execable ~key:edge ~data:true;
        (match CFG.get_data_exn cfg ~label:dest with
        | _ (*bb label*) :: instrs -> 
          let instrs_no_phi = visit_phi_list instrs dest in
          let exec_edge_count = List.fold (CFG.preds cfg dest) ~init:0 
            ~f:(fun acc src -> if Edge_HT.find_exn edge_execable (src,dest) then acc + 1 else acc) in
          if Int.(=) exec_edge_count 1 then
            List.iter instrs_no_phi ~f:(fun instrs -> visit_expression instrs dest); ;
          (match CFG.succs cfg dest with
          | [single_dest] -> 
            Queue.enqueue worklist (Flow (dest,single_dest))
          | dest_l -> 
            (* Assumes the only reason a block with 3 outwards edges exists is if one of them is a 
               "weird exit edge" *)
             if Int.equal (List.length dest_l) 3 then
              (Queue.enqueue worklist (Flow (dest,Label.EXIT_LABEL)))
             else 
              if List.fold_left dest_l ~init:false 
                ~f:(fun acc dest -> acc || (Label.equal dest Label.EXIT_LABEL)) then
                (List.iter dest_l 
                  ~f:(fun single_dest -> (Queue.enqueue worklist (Flow (dest,single_dest))))))
        | [] -> 
          (match CFG.succs cfg dest with
          | [single_dest] -> 
            Queue.enqueue worklist (Flow (dest,single_dest))
          | _ -> ()))); (*Because arith block is empty, must add children*)
      one_iter ()
    | Some SSA (instr,node) ->
      visit_expression instr node;
      one_iter ()
    | None -> ()) in

  one_iter ();

  let cfg_new = CFG.create (CFG.get_fn_label cfg) in
  (* Add all visited edges to new graph *)
  
  Edge_HT.iteri edge_execable 
    ~f:(fun ~key:(pred,succ) ~data -> if data then (CFG.set_succ cfg_new ~pred ~succ));

  let remap_stir stir = 
    (match stir with
    | STIR.Temp t -> (match Temp_HT.find_exn temp_lat_ht t.temp with
      | CONST32 c -> STIR.Imm32 c
      (* | CONST64 c -> STIR.Imm64 c *) (* Left here in case of future changes *)
      | CONST64 _ -> stir (* Only mov can take 64 bit operand *)
      | BOTTOM -> stir
      | TOP -> 
        Printf.printf "\nTop temp:%s\n" (Temp.name t.temp);
        failwith "VALUES SHOULD NEVER BE TOP")
    | _ -> stir) in
  let for_one_label ~label = 
    let rec retemp_instrs instrs = 
      (match instrs with
      | instr :: rest -> 
        (match instr with
        | QWT.Binop b -> 
          (match remap_stir b.dest with 
          (* NOTE: These move can be deleted later if we ever change label type *)
          | STIR.Imm32 c -> 
            (QWT.Mov { dest = b.dest ; src = STIR.Imm32 c }) :: (retemp_instrs rest)
          | STIR.Imm64 c -> 
            (QWT.Mov { dest = b.dest ; src = STIR.Imm64 c }) :: (retemp_instrs rest)
          | dest -> 
            (QWT.Binop { b with dest ; lhs = remap_stir b.lhs ; rhs = remap_stir b.rhs }) 
              :: (retemp_instrs rest))
        | QWT.Unop u -> 
          (* This is done specifically for movsxd *)
          (match remap_stir u.src with
          | STIR.Imm32 c ->  
            let new_temp = STIR.Temp { temp = Temp.create () ; size = A.S_32  } in
            (QWT.Mov { src = STIR.Imm32 c ; dest = new_temp })
            :: (QWT.Unop { u with src = new_temp }) :: (retemp_instrs rest)
          | _ -> instr :: (retemp_instrs rest))
        | QWT.Mov m -> 
          (* NOTE: We could uncomment this if we want useless movs to be eliminated *)
          (* (match remap_stir m.dest with
          | STIR.Imm32 _ -> retemp_instrs rest
          | dest ->  *)
            (QWT.Mov { dest = m.dest ; src = remap_stir m.src }) :: (retemp_instrs rest)
        | QWT.Phi p -> 
          (* have to calculate outer sets first *)
          let new_srcs = STIR_HT.create () in
          let iteri_phi_set ~key:src ~data:pred_set =
            let temp_pred_set = Hash_set.filter pred_set 
              ~f:(fun pred -> Edge_HT.find_exn edge_execable (pred,label)) in
            if Int.(>) (Hash_set.length temp_pred_set) 0 then
              (let insert_src = (match src with
              | STIR.Temp t -> (match Temp_HT.find_exn temp_lat_ht t.temp with
                | CONST32 c -> Some (STIR.Imm32 c)
                | CONST64 c -> Some (STIR.Imm64 c)
                | BOTTOM ->  Some (src)
                | TOP -> None)
              | _ -> Some src) in
              (match insert_src with
              | Some src -> 
                (match STIR_HT.find new_srcs src with
                | Some s -> STIR_HT.set new_srcs ~key:src ~data:(Hash_set.union s temp_pred_set)
                | None -> STIR_HT.set new_srcs ~key:src ~data:temp_pred_set)
              | None -> ())) in
          STIR_HT.iteri p.srcs ~f:iteri_phi_set;
          if Int.(>) (STIR_HT.length new_srcs) 0 then
            (match remap_stir p.dest with
            | STIR.Imm32 _ -> retemp_instrs rest
            | STIR.Imm64 _ -> retemp_instrs rest
            | dest -> (QWT.Phi { dest ; srcs = new_srcs }) :: (retemp_instrs rest))
          else
            retemp_instrs rest
        | QWT.Mem_read m -> 
          (QWT.Mem_read { dest = remap_stir m.dest ; src = remap_stir m.src }) 
            :: (retemp_instrs rest)
        | QWT.Mem_write m -> 
          (QWT.Mem_write { dest = remap_stir m.dest ; src = remap_stir m.src }) 
            :: (retemp_instrs rest)
        | QWT.If i -> 
          (match (Edge_HT.find_exn edge_execable (label,i.if_true),
                  Edge_HT.find_exn edge_execable (label,i.if_false)) with
          | (true,true) -> 
            if Label.equal i.if_true i.if_false then
              (QWT.Goto i.if_true) :: (retemp_instrs rest)
            else
              (QWT.If { i with lhs = remap_stir i.lhs ; rhs = remap_stir i.rhs}) 
                :: (retemp_instrs rest)
          | (false,true) -> (QWT.Goto i.if_false) :: (retemp_instrs rest)
          | (true,false) -> (QWT.Goto i.if_true) :: (retemp_instrs rest)
          | _ -> failwith "At least one conditional branch must be taken")
        | QWT.Return Some r -> 
          (QWT.Return (Some (remap_stir r))) :: (retemp_instrs rest)
        | _ -> instr :: (retemp_instrs rest))
      | [] -> []) in
    CFG.set_data cfg_new ~label ~data:(retemp_instrs (CFG.get_data_exn cfg ~label)) in

  CFG.iter_forward_edge_srcs cfg_new ~f:for_one_label;

  (* Insert all paths to exit *)
  let for_one_exit_pred node = 
    if CFG.mem_label cfg_new node then
      CFG.set_succ cfg_new ~pred:node ~succ:Label.EXIT_LABEL in

  List.iter (CFG.preds cfg Label.EXIT_LABEL) ~f:for_one_exit_pred;
  CFG.set_data cfg_new ~label:Label.EXIT_LABEL ~data:[];

  cfg_new


