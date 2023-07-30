(* Interface for the dataflow framework
 * Author: Elan Biswas <elanb@andrew.cmu.edu>
 *
 * USAGE NOTES: To compute a dataflow analysis, you must first define the dataflow problem. The
 * dataflow problem is a tuple of the following from `Compilers: Principles, Techniques, and Tools,
 * 2nd Edition` 9.3.3:
 *   1. A data flow graph, with ENTRY and EXIT nodes (See cfg.ml)
 *   2. A direction of dataflow `dir` (forwards or backwards)
 *   3. A set of dataflow values V (implicitly given by the types of the operators to follow)
 *   4. A meet operator `meet`, which defines a semilattice on V
 *   5. A family of functions F, where (transfer b) : V -> V in F defines a transfer function on
 *      basic block b. The transfer function must satisfy the property that for all x and y in V,
 *      x <= y ==> f(x) <= f(y) in the partial ordering defined by the meet semilattice. This
 *      guarantees that the analysis will converge on the maximum fixedpoint of the dataflow
 *      equations.
 *   6. A constant function `v_boundary` that outputs a value in V defining the boundary condition.
 *      This is the seed used to propagate dataflow values across flow edges.
 *  Additionally, you must pass a constant function outputting the unique value `top` of the
 *  semilattice such that for all x in V, `meet x top = x` for initialization purposes and an
 *  equality function `eq` for termination condition checking.
 *
 *  The reason for `top` and `v_boundary` being constant functions instead of values outright is
 *  because the values are sometimes mutable data structures, and it is convenient to have a way
 *  to generate fresh instances during the course of the dataflow algorithm.
 *
 *  The result of the analysis is a mapping of each basic block to its IN and OUT dataflow values.
 *)

type 'value in_out = { in_val : 'value ; out_val : 'value }

type direction = FORWARD | BACKWARD

val dataflow_analyze :
    'block Cfg.t
    -> dir : direction
    -> top : (unit -> 'value)
    -> meet:('value -> 'value -> 'value)
    -> transfer : (Cfg.label -> 'value -> 'value)
    -> v_boundary : (unit -> 'value)
    -> eq : ('value -> 'value -> bool)
    -> 'value in_out Cfg.t
    