{
(* L4 Compiler
 * Lexer
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Lexes forward compatible fragment of C0
 *
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Updated to match 2014 spec
 *
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 * Updated to use Core instead of Core.Std and ppx
 *
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Simplify calculation of source location for marking asts.
 *   - Fix eof-in-comment error.
 *   - Keep track of comment nesting level directly in lexer instead of in
 *     mutable state.
 *
 * Update this file to lex the necessary keywords and other tokens
 * in order to make the grammar forward compatible with C0.
 *)

open Core

module T = C0_parser (* Stands for "Token" *)
module Pst = Pst

(* A record of all errors that happened. *)
let errors = Error_msg.create ()

let text = Lexing.lexeme

let from_lexbuf : Lexing.lexbuf -> Mark.src_span option =
  fun lexbuf ->
    Mark.of_positions
      (Lexing.lexeme_start_p lexbuf)
      (Lexing.lexeme_end_p lexbuf)
    |> Option.some

let error lexbuf ~msg : unit =
  let src_span = from_lexbuf lexbuf in
  Error_msg.error errors src_span ~msg

let dec_constant s lexbuf =
  let handle_int_min str =
    if String.equal str "2147483648"
      then "0x80000000"
      else str
  in
  let i32 =
    try Int32.of_string (handle_int_min s)
    with Failure _ ->
      let src_span = from_lexbuf lexbuf in
      Error_msg.error errors src_span
        ~msg:(sprintf "Cannot parse decimal constant `%s`" (text lexbuf));
      Int32.zero
  in
  T.Dec_const i32

let hex_constant s lexbuf =
  let i32 =
    try Int32.of_string s
    with Failure _ ->
      let src_span = from_lexbuf lexbuf in
      Error_msg.error errors src_span
        ~msg:(sprintf "Cannot parse hex constant `%s`" (text lexbuf));
      Int32.zero
  in
  T.Hex_const i32

let lex_ident sym2type name = 
  let sym = Symbol.symbol name in
  if Symbol.Table.mem sym2type sym then T.Type_ident sym else T.Ident sym

}

let ident = ['A'-'Z' 'a'-'z' '_']['A'-'Z' 'a'-'z' '0'-'9' '_']*
let dec_num = ("0" | ['1'-'9'](['0'-'9']*))
let hex_num = "0"['x' 'X']['0'-'9' 'a'-'f' 'A'-'F']+
let reserved_word = 
  ( "assert" | "return" | "bool" | "char" | "int" | "void" | "struct" | "typedef" | "if" | "else"  
  | "while" | "for" | "true" | "false" | "NULL" | "alloc" | "alloc_array" | "string" | "continue" 
  | "break" )

let ws = [' ' '\t' '\r' '\011' '\012']

rule initial sym2type = parse
  | ws+  { initial sym2type lexbuf }
  | '\n' { Lexing.new_line lexbuf;
           initial sym2type lexbuf
         }

  | '{' { T.L_brace }
  | '}' { T.R_brace }
  | '(' { T.L_paren }
  | ')' { T.R_paren }
  | '[' { T.L_brack }
  | ']' { T.R_brack }

  | ';' { T.Semicolon }
  
  | ',' { T.Comma }

  | '.' { T.Dot }
  | "->" { T.R_arrow}

  | '='   { T.Assign }
  | "+="  { T.Plus_eq }
  | "-="  { T.Minus_eq }
  | "*="  { T.Star_eq }
  | "/="  { T.Slash_eq }
  | "%="  { T.Percent_eq }
  | "&="  { T.BitwiseAnd_eq }
  | "^="  { T.BitwiseXor_eq }
  | "|="  { T.BitwiseOr_eq }
  | "<<=" { T.LShift_eq }
  | ">>=" { T.RShift_eq }

  | '+'  { T.Plus }
  | '-'  { T.Minus }
  | '*'  { T.Star }
  | '/'  { T.Slash }
  | '%'  { T.Percent }
  | '<'  { T.LessThan }
  | "<=" { T.LessThanEq }
  | '>'  { T.GreaterThan }
  | ">=" { T.GreaterThanEq }
  | "==" { T.EqualsTo }
  | "!=" { T.NotEqualsTo }
  | "&&" { T.And }
  | "||" { T.Or }
  | '&'  { T.BitwiseAnd }
  | '^'  { T.BitwiseXor }
  | '|'  { T.BitwiseOr }
  | "<<" { T.LShift }
  | ">>" { T.RShift }
  | '!'  { T.Bang }
  | '~'  { T.BitwiseNot }

  | '?'  { T.Question }
  | ':'  { T.Colon }

  | "--" { T.Minus_minus }
  | "++" { T.Plus_plus }

  | "assert" { T.Assert }
  | "return" { T.Return }

  | "bool"    { T.Bool }
  | "char"    { assert false }
  | "int"     { T.Int }
  | "void"    { T.Void }
  | "struct"  { T.Struct }
  | "typedef" { register_typedef_type sym2type lexbuf }

  | "if"    { T.If }
  | "else"  { T.Else }
  | "while" { T.While }
  | "for"   { T.For }

  | "true"  { T.True }
  | "false" { T.False }

  | "NULL"        { T.Null }
  | "alloc"       { T.Alloc }
  | "alloc_array" { T.Alloc_array }

  | "string"   { assert false }
  | "continue" { assert false }
  | "break"    { assert false }

  | dec_num as n { dec_constant n lexbuf }
  | hex_num as n { hex_constant n lexbuf }

  | ident as name { lex_ident sym2type name }

  | "/*" { comment sym2type 1 initial lexbuf }
  | "*/" { error lexbuf ~msg:"Unbalanced comments.";
           initial sym2type lexbuf
         }
  | "//" { comment_line sym2type initial lexbuf }

  | eof { T.Eof }

  | _  { error lexbuf
           ~msg:(sprintf "Illegal character '%s'" (text lexbuf));
         initial sym2type lexbuf
       }

and comment sym2type nesting continuation = parse
  | "/*" { comment sym2type (nesting + 1) continuation lexbuf }
  | "*/" { match nesting - 1 with
           | 0 -> continuation sym2type lexbuf
           | nesting' -> comment sym2type nesting' continuation lexbuf
         }
  | eof  { error lexbuf ~msg:"Reached EOF in comment.";
           T.Eof
         }
  | '\n' { Lexing.new_line lexbuf;
           comment sym2type nesting continuation lexbuf
         }
  | _    { comment sym2type nesting continuation lexbuf }

and comment_line sym2type continuation = parse
  | '\n' { Lexing.new_line lexbuf;
           continuation sym2type lexbuf
         }
  | eof  { error lexbuf ~msg:"Reached EOF in comment.";
           T.Eof
         }
  | _    { comment_line sym2type continuation lexbuf }

and register_typedef_type sym2type = parse
  | ws+ { register_typedef_type sym2type lexbuf }
  | '\n'
    { Lexing.new_line lexbuf;
      register_typedef_type sym2type lexbuf
    }
  | "/*" { comment sym2type 1 register_typedef_type lexbuf }
  | "*/" { error lexbuf ~msg:"Unbalanced comments.";
           register_typedef_type sym2type lexbuf
         }
  | "//" { comment_line sym2type register_typedef_type lexbuf }
  
  | "bool" { register_typedef_ident Pst.Bool sym2type lexbuf }
  | "int" { register_typedef_ident Pst.Int sym2type lexbuf }
  | "struct" { register_typedef_struct sym2type lexbuf }
  | reserved_word as s
    { error lexbuf ~msg:(sprintf "Typedef uses reserved word `%s` as type" s);
      register_typedef_ident Pst.Int sym2type lexbuf
    }
  | ident as t
    { match Symbol.Table.find sym2type (Symbol.symbol t) with
      | None ->
        error lexbuf ~msg:"Typedef uses undefined identifier type" ;
        register_typedef_ident Pst.Int sym2type lexbuf
      | Some t' ->
        register_typedef_ident t' sym2type lexbuf
    }
  | _ as c
    { error lexbuf
        ~msg:(sprintf
          "Expected typedef to be followed by a primitive type or identifier. Instead: `%c`" c) ;
      register_typedef_ident Pst.Int sym2type lexbuf
    }

(* Position in state machine: typedef struct <you are here> ... *)
and register_typedef_struct sym2type = parse
  | ws+ 
    { register_typedef_struct sym2type lexbuf }
  | '\n' 
    { Lexing.new_line lexbuf; register_typedef_struct sym2type lexbuf }
  | "/*" { comment sym2type 1 register_typedef_struct lexbuf }
  | "*/" { error lexbuf ~msg:"Unbalanced comments.";
           register_typedef_struct sym2type lexbuf
         }
  | "//" { comment_line sym2type register_typedef_struct lexbuf }

  | reserved_word as s
    { error lexbuf ~msg:(sprintf "Typedef uses reserved word `%s` as struct name" s);
      register_typedef_ident Pst.Int sym2type lexbuf
    }
  | ident as name
    { register_typedef_ident (Pst.Struct (Symbol.symbol name)) sym2type lexbuf }
  | _ as c
    { error lexbuf
        ~msg:(sprintf
          "Expected typedef to be followed by a primitive type or identifier. Instead: `%c`" c) ;
      register_typedef_ident Pst.Int sym2type lexbuf
    }

(* Position in state machine: typedef <type> <you are here> ... *)
and register_typedef_ident type_ sym2type = parse
  | ws+ 
    { register_typedef_ident type_ sym2type lexbuf }
  | '\n' 
    { Lexing.new_line lexbuf; register_typedef_ident type_ sym2type lexbuf }
  | "/*" { comment sym2type 1 (register_typedef_ident type_) lexbuf }
  | "*/" { error lexbuf ~msg:"Unbalanced comments.";
           register_typedef_ident type_ sym2type lexbuf
         }
  | "//" { comment_line sym2type (register_typedef_ident type_) lexbuf }

  | '*'
    { register_typedef_ident (Pst.Ptr type_) sym2type lexbuf }
  | "[]"
    { register_typedef_ident (Pst.Arr type_) sym2type lexbuf }
  | reserved_word as s
    { error lexbuf ~msg:"Attempted to typedef a reserved word" ;
      T.Typedef (Symbol.symbol s, type_)
    }
  | ident as s 
    { Symbol.Table.set sym2type ~key:(Symbol.symbol s) ~data:type_ ;
      T.Typedef (Symbol.symbol s, type_)
    }
  | _ as c
    { error lexbuf
        ~msg:(sprintf
          "Unexpected character: `%c`" c) ;
      register_typedef_ident Pst.Int sym2type lexbuf
    }

{}
