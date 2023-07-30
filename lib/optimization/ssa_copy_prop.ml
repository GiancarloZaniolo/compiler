(* Copy propagation on SSA
 * 
 * Because of SSA, copy propagation can be done globally, but no instructions are deleted, and
 *  values are not copy propagated into phi functions *)

open Core

module A = Assem
module QWT = Assem.Quad_With_Temps
module STIR = A.Stack_Temp_Imm_Reg
module Label = A.Label
module Label_HS = Label.Hash_set
module CFG = Cfg
module STIR_HT = STIR.Table
module Temp_HT = Temp.Table
module Temp_S = Temp.Set

let ssa_copy_prop (cfg : QWT.program CFG.t) : QWT.program CFG.t = 
  
  let header_key = Temp_HT.create () in
  let child_key = Temp_HT.create () in

  let for_one_mov src dest = 
    (match src with
    | STIR.Temp src_t ->
      let src_head_t = (match Temp_HT.find child_key src_t.temp with
        | Some src_head -> src_head
        | None -> src_t.temp ) in
      let curr_src_set = (match Temp_HT.find header_key src_head_t with
        | Some set -> set
        | None -> Temp_S.singleton src_head_t) in
      (match dest with
      | STIR.Temp dest_t -> 
        let dest_head_t = (match Temp_HT.find child_key dest_t.temp with
        | Some dest_head -> dest_head
        | None -> dest_t.temp ) in
        let curr_dest_set = (match Temp_HT.find header_key dest_head_t with
        | Some set -> set
        | None -> Temp_S.singleton dest_head_t) in
        Temp_HT.set child_key ~key:dest_head_t ~data:src_head_t;
        Temp_HT.set header_key ~key:src_head_t ~data:(Temp_S.union curr_src_set curr_dest_set);
        Temp_HT.set header_key ~key:dest_head_t ~data:Temp_S.empty;
        Temp_S.iter curr_dest_set ~f:(fun e -> Temp_HT.set child_key ~key:e ~data:src_head_t)
      | _ -> failwith "Destination of a move should never not be a temp")
    | _ -> ()) in

  let rec for_one_block instrs = 
    (match instrs with
    | instr :: rest -> (match instr with
      | QWT.Mov m -> 
        for_one_mov m.src m.dest
      | QWT.Phi p -> (match STIR_HT.to_alist p.srcs with
        | [(src,nodes)] -> 
          if Int.equal (Hash_set.length nodes) 1 then
            for_one_mov src p.dest
        | _ -> ())
      | _ -> ());
      for_one_block rest
    | [] -> ()) in 

  CFG.iter cfg ~f:for_one_block;

  let map_copies instrs = 
    let find_copy stir = (match stir with
      | STIR.Temp t -> (match Temp_HT.find child_key t.temp with
        | Some (t_parent) -> STIR.Temp {t with temp = t_parent }
        | _ -> stir)
      | _ -> stir) in
    let rec map_copies_rec instrs acc =
      (match instrs with
      | instr :: rest -> 
        let new_instr = (match instr with
          | QWT.Binop b -> 
            QWT.Binop { b with dest = b.dest ; lhs = find_copy b.lhs ; rhs = find_copy b.rhs }
          | QWT.Unop u -> QWT.Unop { u with dest = u.dest ; src = find_copy u.src }
          | QWT.Mov m -> QWT.Mov { dest = m.dest ; src = find_copy m.src }
          (*| QWT.Phi p -> instr
            (* I am leaving this in just in case we ever fix sa *)
            let new_dest = find_copy p.dest in
            if STIR.equal new_dest p.dest then
              (let srcs_new = STIR_HT.create () in
              let iter_phi ~key ~data = 
                let prop_key = find_copy key in
                (match STIR_HT.find srcs_new prop_key with
                | Some prev_set -> STIR_HT.set srcs_new ~key:prop_key ~data:(Hash_set.union prev_set data)
                | None -> STIR_HT.set srcs_new ~key:prop_key ~data) in
              STIR_HT.iteri p.srcs ~f:iter_phi;
              Some (QWT.Phi { dest = find_copy p.dest ; srcs = srcs_new }))
            else
              None *)
          | QWT.If i -> QWT.If { i with lhs = i.lhs ; rhs = find_copy i.rhs}
          | QWT.Return (Some r) -> QWT.Return (Some (find_copy r))
          | QWT.Mem_read m -> QWT.Mem_read { dest = m.dest ; src = find_copy m.src }
          | QWT.Mem_write m -> QWT.Mem_write { dest = find_copy m.dest ; src = find_copy m.src }
          | QWT.Call _ | QWT.Goto _ | QWT.Label _ | QWT.Directive _ | QWT.Comment _ | QWT.Return _ 
          | QWT.Phi _ -> instr) in

        map_copies_rec rest (new_instr :: acc)
      | [] -> acc) in
    List.rev (map_copies_rec instrs []) in

  CFG.map_data cfg ~f:map_copies