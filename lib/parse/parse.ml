(* L4 Compiler
 * Parsing
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Gluing together the pieces produced by ocamllex and ocamlyacc
 *)

open Core


(* In order for the lexbuf to correctly track source locations
 * we have to initialize the filename in the positions tracked by
 * the lexbuf.
 *)
let initialize_lexbuf (filename : string) : Lexing.lexbuf -> unit =
  let open Lexing in
  let pos = { pos_fname = filename; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 } in
  fun lexbuf ->
    lexbuf.lex_start_p <- pos;
    lexbuf.lex_curr_p <- pos
;;

(* For printing error messages *)
let elab_errors : Error_msg.t = Error_msg.create () ;;
let raise_error ~(msg : string) (ma : 'a Mark.t) = 
  Error_msg.error elab_errors (Mark.src_span ma) ~msg:msg; 
  raise Error_msg.Error 
;;

(* Marks all of the functions declared in the given header PST as external *)
let externalize_header_fns (pst : Pst.program) : Pst.program =
  let rec externalize_rev (rev_acc : Pst.program) (prog : Pst.program) : Pst.program =
  (match prog with
  | [] -> rev_acc
  | mgdecl :: mgdecls -> (match Mark.data mgdecl with
    | Fdecl fdecl ->
      let fdecl' = Pst.Fdecl { fdecl with extern = true } in
      let rev_acc' = (Mark.map ~f:(fun _ -> fdecl') mgdecl) :: rev_acc in
      externalize_rev rev_acc' mgdecls
    | Fdefn _ -> raise_error mgdecl ~msg:"Header function cannot contain function definitions"
    | _ -> externalize_rev (mgdecl :: rev_acc) mgdecls))
  in
  externalize_rev [] pst |> List.rev

(* Parses the input given a header filename string and a source filename string *)
let parse ~(source_filename : string) ~(header_filename : string option) : Pst.program =
  (* The typedef lookup must be created outside build_ast to share it across files *)
  let sym2type = Symbol.Table.create () in
  let build_ast filename =
    In_channel.with_file filename ~f:(fun chan ->
        let lexbuf = Lexing.from_channel chan in
        initialize_lexbuf filename lexbuf;
        try C0_parser.program (C0_lexer.initial sym2type) lexbuf with
        | _ ->
          (* Parse error; attempt to print a helpful error message. *)
          let src_span =
            Mark.of_positions Lexing.(lexbuf.lex_start_p) Lexing.(lexbuf.lex_curr_p)
          in
          Error_msg.error C0_lexer.errors (Some src_span) ~msg:"Parse error.";
          raise Error_msg.Error)
  in
  try
    let header_ast = match header_filename with
    | None -> []
    | Some h_fname -> build_ast h_fname |> externalize_header_fns
    in
    let source_ast = build_ast source_filename in
    if Error_msg.has_any_errors C0_lexer.errors
    then (
      Out_channel.prerr_endline "Lex error.";
      raise Error_msg.Error)
    else List.append header_ast source_ast
  with
  | Sys_error s ->
    (* Probably file not found or permissions errors. *)
    Out_channel.prerr_endline ("System error: " ^ s);
    raise Error_msg.Error
;;


(* ------------------------------------- BEGIN EXPECT TESTS ------------------------------------- *)

let%expect_test "Test parsing of an empty program" =
  let lexbuf =
    Lexing.from_string "int main() {int x = 3; int y = -x + 4; return x + y * x / 3; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     declare(int x = 3)
     declare(int y = binop(unop(-(x)) + 4))
     return binop(x + binop(binop(y * x) / 3));
    }
  |}]
;;

let%expect_test "Text parsing of lvalue wrapped in parens" =
  let lexbuf =
    Lexing.from_string "int main() { int x = 5; (x) = 6; (x); return (x); }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     declare(int x = 5)
     simp(x = 6)
     x
     return x;
    }
  |}]
;;

let%expect_test "Text parsing of unary op combined with binary op in one line" =
  let lexbuf =
    Lexing.from_string "int main() { -x-y; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     binop(unop(-(x)) - y)
    }
  |}]
;;

let%expect_test "Text parsing of dangling else" =
  let lexbuf =
    Lexing.from_string "int main() { if (a) if (b) s; else s2; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     if (a)
     {
      if (b)
      {
       s
      } else
      {
       s2
      }
     }
    }
  |}]
;;

let%expect_test "Text parsing of big paren lvalue" =
  let lexbuf =
    Lexing.from_string "int main() { ((((((((x)))))))) = 7; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     simp(x = 7)
    }
  |}]
;;

let%expect_test "Text parsing of expression wrapped in many parens" =
  let lexbuf =
    Lexing.from_string "int main() { ((((((((x - 1)))))))); }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     binop(x - 1)
    }
  |}]
;;

let%expect_test "Text parsing of a normal for loop" =
  let lexbuf =
    Lexing.from_string "int main() { for (int i =0; i < 10; i++) int x; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     for (declare(int i = 0) ; binop(i < 10) ; simp(i += 1))
     {
      declare(int, x)
     }
    }
  |}]
;;

let%expect_test "Test parsing of just a typedef" =
  let lexbuf =
    Lexing.from_string "typedef int hello;"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    typedef (type: int ; name: hello)
  |}]
;;

let%expect_test "Test parsing of just an fdecl without params" =
  let lexbuf =
    Lexing.from_string "int f();"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdecl(type: int ; name: f ; params: [] ; extern: false);
  |}]
;;

let%expect_test "Test parsing of just an fdecl with params" =
  let lexbuf =
    Lexing.from_string "int f(int x, bool y);"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdecl(type: int ; name: f ; params: [int x, bool y] ; extern: false);
  |}]
;;

let%expect_test "Test parsing of just an fdefn without params and empty body" =
  let lexbuf =
    Lexing.from_string "int f(){}"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: f ; params: [])
    {
    }
  |}]
;;

let%expect_test "Test parsing of just an fdefn with params and simple body" =
  let lexbuf =
    Lexing.from_string "int f(int x, bool y){ int x; x = 6; return x; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: f ; params: [int x, bool y])
    {
     declare(int, x)
     simp(x = 6)
     return x;
    }
  |}]
;;

let%expect_test "Test parsing from a header and source file" =
  let source_filename = "/autograder/dist/compiler/tests/expect/busy.l3" in
  let header_filename = Some "/autograder/dist/compiler/tests/expect/busy.h0" in
  let program = parse ~source_filename ~header_filename in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdecl(type: int ; name: busy_beaver ; params: [int symbols, int states] ; extern: true);
    fdefn(type: int ; name: main ; params: [])
    {
     assert (binop(6 == fn_call(name: busy_beaver ; args: [2, 2])))
     assert (binop(21 == fn_call(name: busy_beaver ; args: [2, 3])))
     assert (binop(107 == fn_call(name: busy_beaver ; args: [2, 4])))
     return fn_call(name: busy_beaver ; args: [4, 2]);
    }
  |}]
;;

let%expect_test "Test parsing of a void fdefn with params and simple body" =
  let lexbuf =
    Lexing.from_string "void f(int x, bool y){ int x; x = 6; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: void ; name: f ; params: [int x, bool y])
    {
     declare(int, x)
     simp(x = 6)
    }
  |}]
;;

let%expect_test "Test parsing of *x++" =
  let lexbuf =
    Lexing.from_string "int main(){ *x++; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     PARSING FAILED
    }
  |}]
;;

let%expect_test "Test parsing of (*x)++" =
  let lexbuf =
    Lexing.from_string "int main(){ (*x)++; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     simp(*x += 1)
    }
  |}]
;;

let%expect_test "Test parsing of arrays" =
  let lexbuf =
    Lexing.from_string "int main(){ int[] x = alloc_array(int, 7+12/3); x[3] = 4; return x[0]; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     declare(int[] x = alloc(int,binop(7 + binop(12 / 3))))
     simp(x[3] = 4)
     return x[0];
    }
  |}]
;;

let%expect_test "Test parsing of pointer declaration/multiplication ambiguity " =
  let lexbuf =
    Lexing.from_string "typedef bool hi; int main(){ hi *x; ho * y; }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    typedef (type: bool ; name: hi)
    fdefn(type: int ; name: main ; params: [])
    {
     declare(hi*, x)
     binop(ho * y)
    }
  |}]
;;

let%expect_test "Test parsing of struct declaration " =
  let lexbuf =
    Lexing.from_string " struct hello; "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    sdecl(name: hello)
  |}]
;;

let%expect_test "Test parsing of struct definition " =
  let lexbuf =
    Lexing.from_string " struct hello { int x; bool[] y; int* z; }; "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    sdefn(name: hello ; params:[int x, bool[] y, int* z])
  |}]
;;

let%expect_test "Test parsing of struct definition with typedef field " =
  let lexbuf =
    Lexing.from_string " typedef int goodbye ; struct hello { int x; bool[] y; goodbye* z; }; "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    typedef (type: int ; name: goodbye)
    sdefn(name: hello ; params:[int x, bool[] y, goodbye* z])
  |}]
;;

let%expect_test "Test parsing of struct accesses" =
  let lexbuf =
    Lexing.from_string " struct hello { int x; bool[] y; };
                         int main() { struct hello h; h.x = 7; h.y = alloc_array(bool, 7); } "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    sdefn(name: hello ; params:[int x, bool[] y])
    fdefn(type: int ; name: main ; params: [])
    {
     declare(struct hello, h)
     simp(h.x = 7)
     simp(h.y = alloc(bool,7))
    }
  |}]
;;

let%expect_test "Test parsing of struct dereferences" =
  let lexbuf =
    Lexing.from_string " struct hello { int x; bool[] y; };
                         int main() { struct hello *h; h->x = 7; h->y = alloc_array(bool, 7); } "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    sdefn(name: hello ; params:[int x, bool[] y])
    fdefn(type: int ; name: main ; params: [])
    {
     declare(struct hello*, h)
     simp(h->x = 7)
     simp(h->y = alloc(bool,7))
    }
  |}]
;;

let%expect_test "Test parsing of pointer deref" =
  let lexbuf =
    Lexing.from_string "int main() { bool *h; *h = true; return *h ? 0 : 1; } "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    fdefn(type: int ; name: main ; params: [])
    {
     declare(bool*, h)
     simp(*h = True)
     return *h ? 0 : 1;
    }
  |}]
;;

let%expect_test "Test parsing of struct pointer typedef" =
  let lexbuf =
    Lexing.from_string
      "
      typedef struct dub* dub;
      int main() {
        // delta = 2000000.001
        dub delta = dadd(itod(2000000), ddiv(itod(1), itod(1000)));
      }"
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    typedef (type: struct dub* ; name: dub)
    fdefn(type: int ; name: main ; params: [])
    {
     declare(dub delta = fn_call(name: dadd ; args: [fn_call(name: itod ; args: [2000000]), fn_call(name: ddiv ; args: [fn_call(name: itod ; args: [1]), fn_call(name: itod ; args: [1000])])]))
    }
  |}]
;;
let%expect_test "Test parsing of typedefined field access" =
  let lexbuf =
    Lexing.from_string "
      typedef struct hoffman jan;
      int main() {
        j.jan;
      }
      "
  in
  let sym2type = Symbol.Table.create () in
  let program = C0_parser.program (C0_lexer.initial sym2type) lexbuf in
  print_endline (Pst.Print.pp_program program);
  [%expect
    {|
    typedef (type: struct hoffman ; name: jan)
    fdefn(type: int ; name: main ; params: [])
    {
     j.jan
    }
  |}]
;;