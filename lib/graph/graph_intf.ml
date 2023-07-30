(* Holds the signature of a Graph. We put it here so that we do not have to duplicate the
 * signature definition the graph.ml and graph.mli files contents
 * 
 * Notes: Graphs are mutable, adding edgess creates vertices
 *
 * Author: Elan Biswas (elanb) 
 *)

module type S  =
sig
    type vertex
    type t

    (* empty (n) ==> initializes a graph of initial capacity n *)
    val create : ?init_capacity:int -> unit -> t

    (* size (g) ==> the number of vertices in the graph *)
    val size : t -> int
    
    (* mem g v ==> true if the given vertex is in the graph, false otherwise *)
    val mem : t -> vertex -> bool  

    (* add_vertex g v ==> Augments g with the vertex v, which has no neighbors *)
    val add_vertex_void : t -> vertex -> unit

    (* add_vertex g v ==> A graph g' that augments g with the vertex v, which has no neighbors *)
    val add_vertex : t -> vertex -> t

    (* Raises an exception if vertex to remove is not contained in the graph *)
    val remove_vertex_exn_void : t -> vertex -> unit

    (* add_directed_edge g src dest ==> Augments g with the edge (from, toward) *)
    val add_directed_edge_void : t -> src:vertex -> dest:vertex -> unit

    (* add_directed_edge g from toward ==> A graph g' that augments g with the edge (from, toward) *)
    val add_directed_edge : t -> src:vertex -> dest:vertex -> t
    
    (* add_undirected_edge g v1 v2 ==> A graph g' that augments g with the edge {v1, v2} *)
    val add_undirected_edge : t -> vertex -> vertex -> t

    (* remove_directed_edge g src dest ==> removes directed edge (from, toward) from g *)
    val remove_directed_edge_void : t -> src:vertex -> dest:vertex -> unit

    (* remove_undirected_edge g src dest ==> removes undirected edge (from, toward) from g *)
    val remove_undirected_edge_void : t -> vertex -> vertex -> unit

    (* add_nbors g v vs ==> A graph g' that augments g with the edges {{v, v'} : v' in vs} *)
    val add_nbors : t -> vertex -> vertex List.t -> t

    (* nbor_list g v ==> a list of the neighbors of vertex v in graph g *)
    val nbor_list : t -> vertex -> vertex List.t

    (* vertex_list g ==> a list of the vertices in graph g *)
    val vertex_list : t -> vertex List.t

    (* Computes a reverse postorder traversal, starting at the given root *)
    val reverse_postorder : t -> root:vertex -> vertex List.t

    (* Iteration function over all vertices *)
    val iter_verts : f:(vertex -> unit) -> t -> unit
  
    val transpose : t -> t

    val pp_graph : t -> v_to_str:(vertex -> string) -> string

    val pp_graphvis_format : t -> v_to_str:(vertex -> string) -> string
end