(* Holds the signature of a Graph that supports vertex coalescing. 
 *
 * "Coalescing" two vertices is defined as combining them into a single vertex whose set of
 * neighbors is the union of the neighbors of the coalesced vertices. Both vertices can still be
 * used to refer to the coalesced vertex and are considered "members" of the graph. Vertices are
 * represented as a collection of "constituent" primitive vertices that have been coalesced into a
 * single vertex (the "representative" vertex). Vertices start out as their own representative and
 * lose this status when they get coalesced into another vertex. i.e The set of constituent vertices
 * is disjoint from the set of representatives.
 *
 * Other typical graph operations include adding and accessing vertices, edges (both directed and
 * undirected), checking if a vertex is a "member" of the graph, and checking if two vertexes form
 * and edge.
 *
 * This interface is in a .intf file to avoid needing to duplicate the interface in the ml and mli
 * graph files.
 *
 * Author: Elan Biswas (elanb) 
 *)

module type S  =
sig
    type vertex
    type t

    (* create ~init_capacity ==> initializes a graph of initial capacity n *)
    val create : ?init_capacity:int -> unit -> t

    (* num_reps (g) ==> the number of (coalesced) vertices in the graph. This is not necessarily
     * the same as the number of vertices represented in graph, which would only be true in the case
     * that the graph is not the result of any coalesce operations *)
    val num_reps : t -> int
    
    (* is_rep_or_constituent g v ==> true iff the given vertex is a either the constituent or
     *                               representative of a coalesced graph node. *)
    val is_rep_or_constituent : t -> vertex -> bool  

    (* add_vertex g v ==> A graph g' that augments g with the vertex v, which has no neighbors *)
    val add_vertex : t -> v:vertex -> t

    (* add_undirected_edge g from toward ==> A graph g' that augments g with the edge (from, toward) *)
    val add_directed_edge : t -> src:vertex -> dest:vertex -> t
    
    (* add_undirected_edge g v1 v2 ==> A graph g' that augments g with the edge {v1, v2} *)
    val add_undirected_edge : t -> v1:vertex -> v2:vertex -> t

    (* add_nbors g v vs ==> A graph g' that augments g with the edges {{v, v'} : v' in vs} *)
    val add_nbors : t -> v:vertex -> nbors:vertex List.t -> t

    (* Augments g with the edges {{v, v'} : v' in vs} *)
    val add_nbors_void : t -> v:vertex -> nbors:vertex List.t -> unit

    (* is_edge g v1 v2 ==> whether {v1, v2} is an edge in g *)
    val is_edge : t -> vertex -> vertex -> bool

    (* coalesce_exn g ~con ~rep ==> an updated graph with the given vertices coalesced, with `con`
     *                              serving as the constituent and `rep` as the representative. *)
    val coalesce_exn : t -> con:vertex -> rep:vertex -> t
    
    (* nbor_rep_list_exn g v ==> a list of the neighboring representative vertices of the
     *                           (representative or constituent) vertex v in graph g.
     * If the given vertex is not a member of the graph, this function raises an exception.  *)
    val nbor_rep_list_exn : t -> vertex -> vertex List.t

    (* rep_degree g v ==> The number of coalesced neighbors the vertex's representative has
     * Raises an exception if the vertex is not a member of the graph.
     *)
    val rep_degree_exn : t -> vertex -> int

    (* get_rep_exn g v ==> The vertex that represents the coalesced node containing this vertex.
     *
     * If this vertex has not been coalesced, then this function is the identity function.
     * Raises an exception if the given vertex is not a member of the graph. *)
    val get_rep_exn : t -> vertex -> vertex

    (* constituents_list_exn g v ==> A list of all vertices represented by the given representative
       vertex. If the given vertex is not a representative, this function raises an exception. *)
    val constituents_list_exn : t -> vertex -> vertex List.t

    (* representatives_list g ==> a list of the representative vertices of graph g
     * A representative corresponds to a coalesced node of one or more constituenet vertices *)
    val representatives_list : t -> vertex List.t

    (* Convert the graph into a string representation *)
    val pp_graph : t -> v_to_str:(vertex -> string) -> string 

    val pp_graphvis_format : t ->  v_to_str:(vertex -> string) -> string
end
