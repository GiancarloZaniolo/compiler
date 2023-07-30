(* L4 Compiler
 * TypeChecker
 * Author: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Simple typechecker that is based on a unit Symbol.table
 * This is all that is needed since there is only an integer type present
 * Also, since only straightline code is accepted, we hack our way
 * around initialization checks here.
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now distinguishes between declarations and initialization
 *)

(* prints error message and raises ErrorMsg.error if error found *)

(* module A = Ast *)
open Core
module SHT : Hashtbl.S with type key = Symbol.t


type init_status =
| Decl
| Init

type fdecl_status = 
{ fdecl : Ast.fdecl
; init_status : init_status
; used : bool }

type gdecl_ctxts = 
  { fdecl_ctxt : fdecl_status SHT.t
  ; typedef_ctxt : Ast.type_ SHT.t }

val typecheck : Ast.program -> (Ast.program * gdecl_ctxts)
