(* Graph library implementation that maps vertices to (hash) sets of their neighbors via a hash
 * table.
 * Author: Elan Biswas (elanb)
 *)
open Core

let init_nbor_set_size = 20
let init_graph_size = 20

include Graph_intf

module Make_Hash_Graph (H : Hashable.S) : S with type vertex := H.t =
struct
  module VM = H.Table
  module VS = H.Hash_set
  type vertex = H.t

  type t = VS.t VM.t

  let create ?(init_capacity=init_graph_size) _ = VM.create () ~size:init_capacity ;;
  
  let size g = VM.length g

  let mem g v = VM.mem g v

  let add_directed_edge_void g ~src ~dest =
    let add_nbor (v : vertex) (s : VS.t) : unit = Hash_set.add s v in
    let add_v_with_nbor (nbor : vertex) (v : vertex) : unit = 
      let nbors : VS.t = VS.create ~growth_allowed:true ~size:init_nbor_set_size () in
      Hash_set.add nbors nbor; 
      VM.add_exn g ~key:v ~data:nbors
    in
    VM.find_and_call g src ~if_found:(add_nbor dest) ~if_not_found:(add_v_with_nbor dest)
    
  let add_undirected_edge_void g v1 v2 = 
     (* We want to add each vertex to each other's neighbor set *)
    add_directed_edge_void g ~src:v1 ~dest:v2;
    add_directed_edge_void g ~src:v2 ~dest:v1;
  ;;

  let add_vertex_void g v =
    let add_empty_set v' =
      let nbor_set = VS.create ~growth_allowed:true () in
      VM.add_exn g ~key:v' ~data:nbor_set
    in
    VM.find_and_call g v ~if_found:(fun _ -> ()) ~if_not_found:add_empty_set
    
  let add_vertex g v = add_vertex_void g v ; g

  let remove_vertex_exn_void g v =
    let remove_v nbor_set = Hash_set.remove nbor_set v in
    VM.iter g ~f:remove_v ;
    VM.remove g v

  let add_directed_edge g ~src ~dest = add_directed_edge_void g ~src:src ~dest:dest ; g ;;

  let add_undirected_edge g v1 v2 = add_undirected_edge_void g v1 v2 ; g ;;

  let remove_directed_edge_void g ~src ~dest =
    let rem_nbor (v : vertex) (s : VS.t) : unit = Hash_set.remove s v in
    VM.find_and_call g src ~if_found:(rem_nbor dest) ~if_not_found:(fun _ -> ())
  ;;

  let remove_undirected_edge_void g v1 v2 = 
    (* We want to add each vertex to each other's neighbor set *)
    remove_directed_edge_void g ~src:v1 ~dest:v2;
    remove_directed_edge_void g ~src:v2 ~dest:v1;
  ;;

  let add_nbors g v vs = List.iter ~f:(add_undirected_edge_void g v) vs ; g ;;

  let nbor_list g v = 
    VM.find_and_call g v ~if_found:(fun s -> Hash_set.to_list s) ~if_not_found:(fun _ -> [])
  ;; 

  let vertex_list g = VM.keys g ;;

(* Post-order traversal algorithm from 
 * https://eli.thegreenplace.net/2015/directed-graph-traversal-orderings-and-applications-to-data-flow-analysis/ *)
  let reverse_postorder g ~root =
  let visited = VS.create () in
  let order = Stack.create () in
  let rec dfs_walk (node : vertex) : unit =
    Hash_set.add visited node ;
    let visit_succ succ =
      if not (Hash_set.mem visited succ) then dfs_walk succ else ()
    in
    List.iter (nbor_list g node) ~f:visit_succ ;
    Stack.push order node
  in
  dfs_walk root ;
  Stack.to_list order

  let iter_verts ~f g = 
    VM.iter_keys g ~f

  let transpose (g : t) : t =
    let transpose_g = create () in
    let reverse_edges v nbors =
      Hash_set.iter nbors ~f:(fun n -> add_directed_edge_void transpose_g ~src:n ~dest:v)
    in
    VM.iteri g ~f:(fun ~key ~data -> reverse_edges key data) ;
    transpose_g
  
  let pp_graph (g : t) ~(v_to_str : vertex -> string) : string = 
    let pp_pair (v, s) = sprintf "%s -> [%s])"
      (v_to_str v) (Hash_set.to_list s |> Print_utils.pp_list ~f:v_to_str)
    in
    sprintf "GRAPH:\n%s\n_END_GRAPH" 
      (Print_utils.pp_list ~sep:"\n\n" ~f:pp_pair (VM.to_alist g))
  ;;

  let pp_graphvis_format (g : t) ~(v_to_str : vertex -> string) : string =
    let pp_edge (v, u) = sprintf "\t%s -> %s;" (v_to_str v) (v_to_str u) in
    let pp_all_edges (v, s) =
      Hash_set.to_list s |> List.map ~f:(fun u -> (v, u))
      |> Print_utils.pp_list ~sep:"\n" ~f:pp_edge
    in
    sprintf "digraph G {\n%s\n\t%s;\n}"
      (VM.to_alist g |> Print_utils.pp_list ~f:pp_all_edges ~sep:"\n")
      (VM.keys g |> Print_utils.pp_list ~f:(v_to_str) ~sep:";\n\t")
end

(* -------------------------------- BEGIN EXPECT TESTS -------------------------------- *)
(* module RTI = Assem.Reg_Temp_Imm
let%expect_test "Test parsing of an empty program" =
  let module Operand_Graph = Make_Hash_Graph(RTI) in
  let g : Operand_Graph.t = Operand_Graph.create () in
  Temp.reset () ;
  let v1 = RTI.Temp (Temp.create ()) in
  let v2 = RTI.Reg `EAX in
  let _ : Operand_Graph.t = Operand_Graph.add_undirected_edge g v1 v2 in
  let print_nbors g v = 
    let vstr = RTI.format_operand v in
    let nbors = Operand_Graph.nbor_list g v in
    print_endline ("Neighbors of " ^ vstr ^ ": " ^ List.to_string ~f:RTI.format_operand nbors);
  in
  print_nbors g v1;
  print_nbors g v2;

  [%expect
    {|
    Neighbors of %t1: (%eax)
    Neighbors of %eax: (%t1)
  |}]
;; *)
