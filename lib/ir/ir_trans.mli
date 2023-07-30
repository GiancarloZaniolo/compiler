(* Interface for the translations of ASTs into IRTs
 * Author: Giancarlo Zaniolo
 * Modified: Elan Biswas
 *   - Removed unnecessaryr module definitions
 *)

 val translate : Ast.program -> Typechecker.gdecl_ctxts -> Ir_tree.program 
