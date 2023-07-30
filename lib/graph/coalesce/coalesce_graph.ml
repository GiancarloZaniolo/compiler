(* Graph library implementation that maps vertices to hash sets of their neighbors via a hash
 * table.
 * Author: Elan Biswas (elanb)
 *)
open Core

let init_nbor_set_size = 20
let init_graph_size = 20

include Coalesce_graph_intf

module Make_Hash_Graph (H : Hashable.S) : S with type vertex := H.t =
struct
  module VM = H.Table
  module VS = H.Hash_set
  type vertex = H.t
  (* A graph is a collection of adjacency sets, and association of constituent and representative
    vertices. This association is used to save which vertices get coalesced together. *)
  type t = { edges : VS.t VM.t ; vert_to_rep : vertex VM.t ; rep_to_verts : VS.t VM.t }

  let create ?(init_capacity=init_graph_size) _ =
    let create _ = VM.create () ~growth_allowed:true ~size:init_capacity in
    let edges = create () and vert_to_rep = create () and rep_to_verts = create () in
    { edges ; vert_to_rep ; rep_to_verts }
  ;;
  
  let num_reps g = VM.length g.edges ;;

  let is_rep_or_constituent g v = VM.mem g.vert_to_rep v ;;

  (* Get the vertex representing a coalesced node containing the given vertex *)
  let get_rep_exn (g : t) (v : vertex) : vertex = VM.find_exn g.vert_to_rep v ;;

  (* Get the nodes represented in the coalesced node represented by the given vertex *)
  let constituents_list_exn (g : t) (v : vertex) : vertex List.t = 
    VM.find_exn g.rep_to_verts v |> Hash_set.to_list ;;

  (* Get the nodes represented in the coalesced node represented by the given vertex *)
  let constituents_set_exn (g : t) (v : vertex) : VS.t = VM.find_exn g.rep_to_verts v ;;

  let get_nbor_set_exn (g : t) (v : vertex) : VS.t = VM.find_exn g.edges (get_rep_exn g v) ;;

  let is_edge g v1 v2 =
    if not((is_rep_or_constituent g v1) && (is_rep_or_constituent g v2)) then
      false
    else
      let v1_rep = get_rep_exn g v1 in
      let v2_rep = get_rep_exn g v2 in
      let v1_nbors = get_nbor_set_exn g v1_rep in
      let v2_nbors = get_nbor_set_exn g v2_rep in
      (Hash_set.mem v1_nbors v2_rep) && (Hash_set.mem v2_nbors v1_rep)
  ;;
  let add_vertex_if_not_present_void (g : t) (v : vertex) : unit =
    let add_empty_set_and_self_map v' =
      let nbor_set = VS.create ~growth_allowed:true ~size:init_nbor_set_size () in
      VM.add_exn g.vert_to_rep ~key:v' ~data:v' ;
      VM.add_exn g.edges ~key:v' ~data:nbor_set ;
      VM.add_exn g.rep_to_verts ~key:v' ~data:(VS.of_list [v'])
    in
    VM.find_and_call g.vert_to_rep v
      ~if_found:(fun _ -> ()) ~if_not_found:add_empty_set_and_self_map

  let add_directed_edge_void g ~src ~dest =
    add_vertex_if_not_present_void g src ;
    add_vertex_if_not_present_void g dest ;
    let src_rep = get_rep_exn g src in
    let dest_rep = get_rep_exn g dest in
    let add_nbor (v : vertex) (s : VS.t) : unit = Hash_set.add s v in
    VM.find_and_call g.edges src_rep 
      ~if_found:(add_nbor dest_rep)
      ~if_not_found:(fun _ -> failwith "Should be present")
  ;;
    
  let add_undirected_edge_void g v1 v2 = 
    (* We want to add each vertex to each other's neighbor set *)
    add_directed_edge_void g ~src:v1 ~dest:v2 ;
    add_directed_edge_void g ~src:v2 ~dest:v1 ;
  ;;

  let add_vertex g ~v = add_vertex_if_not_present_void g v ; g ;;

  let add_directed_edge g ~src ~dest = add_directed_edge_void g ~src:src ~dest:dest ; g ;;

  let add_undirected_edge g ~v1 ~v2 = add_undirected_edge_void g v1 v2 ; g ;;

  let add_nbors_void g ~v ~nbors:vs = List.iter ~f:(add_undirected_edge_void g v) vs ;;
  
  let add_nbors g ~v ~nbors = add_nbors_void g ~v ~nbors ; g ;;

  let coalesce_exn g ~con ~rep =
    let con_node = get_rep_exn g con in
    let rep_node = get_rep_exn g rep in
    let coalesced_nbors =
      Hash_set.union (get_nbor_set_exn g con_node) (get_nbor_set_exn g rep_node)
    in
    (* Remove must be before set b/c user might try to coalesce vertices that have already
       been coalesced. In this case, the vertex would be removed from the edge mapping otherwise. *)
    VM.remove g.edges con_node ; 
    VM.set g.edges ~key:rep_node ~data:coalesced_nbors ;
    VM.filter g.edges ~f:(fun s -> Hash_set.mem s con_node) 
    |> VM.iter ~f:(fun s -> Hash_set.remove s con_node ; Hash_set.add s rep_node) ;

    let con_node_constituents = constituents_set_exn g con_node in
    let rep_node_constituents = constituents_set_exn g rep_node in
    let coalesced_constituents = Hash_set.union (con_node_constituents) (rep_node_constituents) in
    Hash_set.add coalesced_constituents con_node ;
    (* Remove must be before set for same reason here *)
    VM.remove g.rep_to_verts con_node ;
    VM.set g.rep_to_verts ~key:rep_node ~data:coalesced_constituents ;

    (* This must happen after coalescing the neighbor sets because updating a vertex's
       representative will change its neighbor set *)
    Hash_set.iter coalesced_constituents ~f:(fun c -> VM.set g.vert_to_rep ~key:c ~data:rep_node) ;
    g
  ;;

  let nbor_rep_list_exn g v = 
    let node = get_rep_exn g v in
    VM.find_and_call g.edges node ~if_found:Hash_set.to_list ~if_not_found:(fun _ -> [])
  ;; 

  let rep_degree_exn (g : t) (v : vertex) : int = nbor_rep_list_exn g v |> List.length
  ;;

  let representatives_list g = VM.keys g.edges ;;

  let pp_graph g ~v_to_str = 
    let set_to_str s = sprintf "{%s}" (Hash_set.to_list s |> Print_utils.pp_list ~f:v_to_str) in
    let pp_nbor_list nbors =
      List.map ~f:(constituents_set_exn g) nbors |> Print_utils.pp_list ~f:set_to_str
    in
    let pp_pair (v, s) = sprintf "%s -> [%s])"
      (constituents_set_exn g v |> set_to_str) (Hash_set.to_list s |> pp_nbor_list)
    in
    sprintf "GRAPH:\n%s\n_eND_GRAPH" 
      (Print_utils.pp_list ~sep:"\n\n" ~f:pp_pair (VM.to_alist g.edges))
  ;;

  let pp_graphvis_format (g : t) ~(v_to_str : vertex -> string) : string =
    let without_special_chars v =
      v_to_str v
      |> String.substr_replace_all ~pattern:"%" ~with_:""
      |> String.substr_replace_all ~pattern:"S_64" ~with_:""
      |> String.substr_replace_all ~pattern:"_" ~with_:""
    in
    let pp_vertex_list = Print_utils.pp_list ~f:without_special_chars in
    let tab = "  " in
    let pp_edge (v, u) =
      sprintf "\t%s -> %s;" (without_special_chars v) (without_special_chars u)
    in
    let pp_all_edges (v, s) =
      Hash_set.to_list s |> List.map ~f:(fun u -> (v, u))
      |> Print_utils.pp_list ~sep:"\n" ~f:pp_edge
    in
    let rep_to_subgraph rep =
      sprintf "%ssubgraph cluster_%s {\n%s%slabel=\"%s\";\n%s%s%s;\n%s}"
        tab (* subgraph *) (without_special_chars rep) (* { *)
        tab tab (* label=" "*) (constituents_list_exn g rep |> pp_vertex_list)
        tab tab (without_special_chars rep)
        tab (* } *)
    in
    sprintf "digraph G {\n%s\n%s\n}"
      (VM.keys g.rep_to_verts |> Print_utils.pp_list ~sep:"\n" ~f:rep_to_subgraph)
      (VM.to_alist g.edges |> Print_utils.pp_list ~f:pp_all_edges ~sep:"\n")
end


(* TODO: Fix these probably maybe later *)
(* -------------------------------- BEGIN EXPECT TESTS -------------------------------- *)
(* module STIR = Assem.Stack_Temp_Imm_Reg
let%expect_test "Test simple graph construction" =
  Temp.reset () ;
  let module Operand_Graph = Make_Hash_Graph(STIR) in
  let g : Operand_Graph.t = Operand_Graph.create () in
  Temp.reset () ;
  let v1 = STIR.Temp (Temp.create ()) in
  let v2 = STIR.Reg EAX in
  let g' : Operand_Graph.t = Operand_Graph.add_undirected_edge g ~v1 ~v2 in
  Operand_Graph.pp_graph g' ~v_to_str:STIR.format_operand |> prerr_endline ;

  [%expect
    {|
    GRAPH:
    {%EAX} -> [{%t1}])

    {%t1} -> [{%EAX}])
    END_GRAPH
  |}]
;; 

let%expect_test "Test simple coalescing" =
  Temp.reset () ;
  let module Operand_Graph = Make_Hash_Graph(STIR) in
  let g : Operand_Graph.t = Operand_Graph.create () in
  Temp.reset () ;
  let v1 = STIR.Reg R9D in
  let v2 = STIR.Reg R10D in
  let v3 = STIR.Reg R11D  in
  let v4 = STIR.Reg R12D in
  let g' : Operand_Graph.t = 
    Operand_Graph.add_undirected_edge g ~v1 ~v2
    |> Operand_Graph.add_undirected_edge ~v1:v3 ~v2:v4
    |> Operand_Graph.coalesce_exn ~v:v3 ~rep:v2
  in
  Operand_Graph.pp_graph g' ~v_to_str:STIR.format_operand |> prerr_endline ;

  [%expect
    {|
    GRAPH:
    {%R12D} -> [{%R11D, %R10D}])

    {%R11D, %R10D} -> [{%R12D}, {%R9D}])

    {%R9D} -> [{%R11D, %R10D}])
    END_GRAPH
  |}]
;;

let%expect_test "Test coalescing of two coalesced nodes" =
  Temp.reset () ;
  let module Operand_Graph = Make_Hash_Graph(STIR) in
  let g : Operand_Graph.t = Operand_Graph.create () in
  Temp.reset () ;
  let r9D = STIR.Reg R9D in
  let r10D = STIR.Reg R10D in
  let r11D = STIR.Reg R11D  in
  let r12D = STIR.Reg R12D in
  let r13D = STIR.Reg R13D in
  let r14D = STIR.Reg R14D in
  let g' : Operand_Graph.t = 
    Operand_Graph.add_undirected_edge g ~v1:r9D ~v2:r10D
    |> Operand_Graph.add_undirected_edge ~v1:r11D ~v2:r12D
    |> Operand_Graph.add_undirected_edge ~v1:r13D ~v2:r14D
    |> Operand_Graph.coalesce_exn ~v:r11D ~rep:r10D
    |> Operand_Graph.coalesce_exn ~v:r12D ~rep:r14D
  in
  Operand_Graph.pp_graph g' ~v_to_str:STIR.format_operand |> prerr_endline ;

  [%expect
    {|
    GRAPH:
    {%R11D, %R10D} -> [{%R14D, %R12D}, {%R9D}])

    {%R9D} -> [{%R11D, %R10D}])

    {%R14D, %R12D} -> [{%R11D, %R10D}, {%R13D}])

    {%R13D} -> [{%R14D, %R12D}])
    END_GRAPH
  |}]
;;
*)
