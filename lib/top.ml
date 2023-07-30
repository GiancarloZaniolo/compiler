(* L4 Compiler
 * Top Level Environment
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Alex Vaynberg <alv@andrew.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 * Modified: Alice Rao <alrao@andrew.cmu.edu>
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Use Cmdliner instead of Getopt for command-line parsing.
 * Modified: Henry Nelson <hcnelson99@gmail.com>
 *   - Switch from ocamlbuild to dune 2.7
 *   - TODO: Add support for expect tests
 *   - Update to Core v0.14
 *)

open Core
module QWT = Assem.Quad_With_Temps
module QR = Assem.Quad_Regalloc
module STIR = Assem.Stack_Temp_Imm_Reg

(* Command line arguments *)

module Opt_level = struct
  type t =
    | Opt_none
    | Opt_one
    | Opt_two
    | Opt_three
  [@@deriving equal]

  let show = function
    | Opt_none -> "O0"
    | Opt_one -> "O1"
    | Opt_two -> "O2"
    | Opt_three -> "O3"
  ;;

  let parse = function
    | "0" -> Result.Ok Opt_none
    | "1" -> Result.Ok Opt_one
    | "2" -> Result.Ok Opt_two 
    | "3" -> Result.Ok Opt_three
    | arg -> Result.Error (`Msg ("Error: Unknown --opt arg: " ^ arg))
  ;;

  let conv =
    let print ppf opt = Format.fprintf ppf "%s" (show opt) in
    Cmdliner.Arg.conv (parse, print)
  ;;
end

module Emit = struct
  type t =
    | X86_64
    | ARM_64
    | Abstract_assem
    | LLVM
    [@@deriving equal]

  let show = function
    | X86_64 -> "x86-64"
    | Abstract_assem -> "abs"
    | LLVM -> "llvm"
    | ARM_64  -> "arm64"
  ;;

  let parse = function
    | "abs" -> Result.Ok Abstract_assem
    | "x86-64" -> Result.Ok X86_64
    | "llvm" -> Result.Ok LLVM
    | "arm64" -> Result.Ok ARM_64
    | arg -> Result.Error (`Msg ("Unknown emit arg: " ^ arg))
  ;;

  let conv =
    let print ppf emit = Format.fprintf ppf "%s" (show emit) in
    Cmdliner.Arg.conv (parse, print)
  ;;
end

type cmd_line_args =
  { verbose : bool
  ; dump_parsing : bool
  ; dump_pst : bool
  ; dump_ast : bool
  ; dump_tst : bool
  ; dump_ir : bool
  ; dump_assem : bool
  ; dump_ssa : bool
  ; dump_sccp : bool
  ; dump_copy : bool
  ; dump_adce : bool
  ; dump_conv : bool
  ; dump_cfg : bool
  ; dump_pre_ssa : bool
  ; dump_pre_regalloc : bool
  ; dump_regalloc : bool
  ; typecheck_only : bool
  ; regalloc_only : bool
  ; unsafe : bool
  ; emit : Emit.t
  ; opt_level : Opt_level.t
  ; filename : string
  ; header_filename : string option
  ; no_ssa : bool
  ; no_sccp : bool
  ; no_global_copy_prop : bool
  ; no_adce : bool
  ; no_const_copy_prop : bool
  ; no_pre : bool
  ; add_pre_after_ssa : bool
  ; no_peephole : bool
  ; no_clean_control : bool
  ; no_tail_recursion : bool
  ; ssa_opt_iters : int
  }

(* A term (using the vocabulary of the Cmdliner library) that can be used to
 * parse command-line arguments. *)
let cmd_line_term : cmd_line_args Cmdliner.Term.t =
  let open Cmdliner in
  (* See https://github.com/janestreet/ppx_let *)
  (* This allows a more convenient syntax for using the Cmdliner
   * library: If we use let%map instead of normal "let", and we
   * have a declaration of the form:
   *
   * let%map x = e1 in e2
   *
   * even if e1 is of type 'a Term.t, we can use x as having type 'a
   * in the body of e2.
   *)
  let module Let_syntax = struct
    let return = Term.const
    let map ~f a = Term.(return f $ a)
    let both a b = Term.(const Tuple2.create $ a $ b)
  end
  in
  let flag info = Arg.value (Arg.flag info) in
  let opt conv ~default info = Arg.value (Arg.opt conv default info) in
  let%map verbose =
    let doc = "If present, print verbose debug information." in
    flag (Arg.info [ "v"; "verbose" ] ~doc)
  and dump_parsing =
    let doc = "If present, print debug informaton from parsing." in
    flag (Arg.info [ "dump-parsing" ] ~doc)
  and dump_pst =
    let doc = "If present, print the parsed pst." in
    flag (Arg.info [ "dump-pst" ] ~doc)
  and dump_ast =
    let doc = "If present, print the parsed ast." in
    flag (Arg.info [ "dump-ast" ] ~doc)
  and dump_tst =
    let doc = "If present, print the parsed tst." in
    flag (Arg.info [ "dump-tst" ] ~doc)
  and dump_ir =
    let doc = "If present, print the translated IR tree." in
    flag (Arg.info [ "dump-ir" ] ~doc)
  and dump_assem =
    let doc = "If present, print the initial quad assembly translation of the IR tree." in
    flag (Arg.info [ "dump-assem" ] ~doc)
  and dump_ssa =
    let doc = "If present, print the assembly after SSA construction" in
    flag (Arg.info [ "dump-ssa" ] ~doc)
  and dump_sccp =
    let doc = "If present, print the assembly after SSA optimizations" in
    flag (Arg.info [ "dump-sccp" ] ~doc)
  and dump_copy =
    let doc = "If present, print the assembly after copy propagation optimization" in
    flag (Arg.info [ "dump-copy" ] ~doc)
  and dump_adce =
    let doc = "If present, print the assembly after SSA optimizations" in
    flag (Arg.info [ "dump-adce" ] ~doc)
  and dump_conv =
    let doc =
      "If present, print the assembly after adding in C ABI calling conventions."
    in
    flag (Arg.info [ "dump-conv" ] ~doc)
  and dump_cfg =
    let doc = "If present, print the CFG after convention translation." in
    flag (Arg.info [ "dump-cfg" ] ~doc)
  and dump_regalloc =
    let doc = "If present, print the pseudo-assembly after register allocation." in
    flag (Arg.info [ "dump-regalloc" ] ~doc)
  and dump_pre_ssa =
    let doc = "If present, print the pseudo-assembly just before SSA translation." in
    flag (Arg.info [ "dump-pre-ssa" ] ~doc)
  and dump_pre_regalloc =
    let doc = "If present, print the pseudo-assembly just before register allocation." in
    flag (Arg.info [ "dump-pre-regalloc" ] ~doc)
  and typecheck_only =
    let doc = "If present, exit after typechecking." in
    flag (Arg.info [ "t"; "typecheck-only" ] ~doc)
  and regalloc_only =
    let doc = "Regalloc only for l1 checkpoint" in
    flag (Arg.info [ "r"; "regalloc-only" ] ~doc)
  and unsafe =
    let doc = "Compile without null or bounds checks on memory operations" in
    flag (Arg.info [ "unsafe" ] ~doc)
  and emit0 =
    let doc = "[abs|x86-64|arm64|llvm] The type of assembly $(docv) to emit." in
    opt
      Emit.conv
      ~default:Emit.Abstract_assem
      (Arg.info [ "e"; "emit" ] ~doc ~docv:"TARGET")
  and opt_level =
    let doc = "[0|1|2] The optimization level $(docv)." in
    opt
      Opt_level.conv
      ~default:Opt_level.Opt_one
      (Arg.info [ "O"; "opt" ] ~doc ~docv:"OPT")
  and filename =
    let doc = "The source file $(docv) to compile." in
    Arg.(required (pos 0 (some non_dir_file) None (info [] ~doc ~docv:"FILE")))
  and header_filename =
    let doc = "The header file $(docv) to compile" in
    opt Arg.(some non_dir_file) ~default:None (Arg.info [ "l" ] ~doc ~docv:"FILE")
  and no_ssa =
    let doc = "Compile without SSA translation" in
    flag (Arg.info [ "no-ssa" ] ~doc)
  and no_sccp =
    let doc = "Compile without sparse conditional constant propagation" in
    flag (Arg.info [ "no-sccp" ] ~doc)
  and no_global_copy_prop =
    let doc = "Compile without copy propagation on SSA" in
    flag (Arg.info [ "no-global-copy-prop" ] ~doc)
  and no_adce =
    let doc = "Compile without agressive dead code elimination" in
    flag (Arg.info [ "no-adce" ] ~doc)
  and no_const_copy_prop =
    let doc = "Compile without constand and copy propagation not on SSA" in
    flag (Arg.info [ "no-const-copy-prop" ] ~doc)
  and no_pre =
    let doc = "Compile without partial redundancy elimination SSA" in
    flag (Arg.info [ "no-pre" ] ~doc)
  and add_pre_after_ssa =
    let doc = "Compile with partial redundancy elimination after SSA" in
    flag (Arg.info [ "add-pre-after-ssa" ] ~doc)
  and no_peephole =
    let doc = "Compile without any peephole optimizations" in
    flag (Arg.info [ "no-peephole" ] ~doc)
  and no_clean_control =
    let doc = "Compile without control flow cleaning" in
    flag (Arg.info [ "no-clean-control" ] ~doc)
  and no_tail_recursion =
    let doc = "Compile without tail recursion" in
    flag (Arg.info [ "no-tail-recursion" ] ~doc)
  and ssa_opt_iters =
    let doc = "Number of iterations of SCCP, global copy propagation, and ADCE" in
    let conv = 
      let show = Int.to_string in
      let print ppf opt  = Format.fprintf ppf "%s" (show opt) in
      let parse = fun a -> Result.Ok (Int.of_string a) in
      Cmdliner.Arg.conv (parse,print) in
    opt conv ~default:1 (Arg.info [ "ssa-opt-iters" ] ~doc)
  and llvm =
    let doc = "Compile to llvm bytecode" in
    flag (Arg.info [ "llvm" ] ~doc)
  in
  let emit = if llvm then Emit.LLVM else emit0 in
  { verbose
  ; dump_parsing
  ; dump_pst
  ; dump_ast
  ; dump_tst
  ; dump_ir
  ; dump_assem
  ; dump_ssa
  ; dump_sccp
  ; dump_copy
  ; dump_adce
  ; dump_conv
  ; dump_cfg
  ; dump_pre_ssa
  ; dump_pre_regalloc
  ; dump_regalloc
  ; typecheck_only
  ; regalloc_only
  ; unsafe
  ; emit
  ; opt_level
  ; filename
  ; header_filename
  ; no_ssa
  ; no_sccp
  ; no_global_copy_prop
  ; no_adce
  ; no_const_copy_prop
  ; no_pre
  ; add_pre_after_ssa
  ; no_peephole
  ; no_clean_control
  ; no_tail_recursion
  ; ssa_opt_iters
  }
;;

let say_if (v : bool) (f : unit -> string) = if v then prerr_endline (f ())


(* The main driver for the compiler: runs each phase. *)
let compile (cmd : cmd_line_args) : unit =
  say_if cmd.verbose (fun () -> "Parsing... " ^ cmd.filename);
  if cmd.dump_parsing then ignore (Parsing.set_trace true : bool);
  (* Parse *)
  let pst =
    Parse.parse ~source_filename:cmd.filename ~header_filename:cmd.header_filename
  in
  say_if cmd.dump_pst (fun () -> Pst.Print.pp_program pst);
  (* Elaborate *)
  let ast = Elaborate.elaborate pst in
  say_if cmd.dump_ast (fun () -> Ast.Print.pp_program ast);
  (* Typecheck *)
  say_if cmd.verbose (fun () -> "Checking...");
  let tc_ast, gdecl_ctxts = Typechecker.typecheck ast in
  say_if cmd.dump_tst (fun () -> Ast.Print.pp_program tc_ast);
  if cmd.typecheck_only then exit 0;
  (* Translate *)
  say_if cmd.verbose (fun () -> "Translating...");
  let ir = Ir_trans.translate tc_ast gdecl_ctxts in
  say_if cmd.dump_ir (fun () -> Ir_tree.Print.pp_program ir);
  (* Codegen *)
  say_if cmd.verbose (fun () -> "Codegen...");
  let will_use_llvm =
    Emit.(equal LLVM cmd.emit || equal ARM_64 cmd.emit)
    || Opt_level.(equal cmd.opt_level Opt_two)
    || Opt_level.(equal cmd.opt_level Opt_three)
  in
  let assem = Three_addr_trans.codegen ir cmd.unsafe will_use_llvm in
  say_if cmd.dump_assem (fun () -> Print_utils.pp_list ~f:QWT.format ~sep:"\n" assem);

  say_if cmd.verbose (fun () -> "Translating to CFG...");
  let cfgs = ref(Cfg_trans.quad_to_cfg assem) in
  say_if cmd.dump_cfg (fun () -> Cfg.Print.pp_cfgs_graphvis_format !cfgs);

  let ll_file = cmd.filename ^ ".ll" in
  let llvm_setup _ : unit =
    say_if cmd.verbose (fun () -> "Translating to SSA...");
    List.iter !cfgs ~f:Ssa_trans.create_ssa;
    let purity_fn =
      if (not cmd.no_ssa) && not cmd.no_adce then 
        Puree_analysis.puree_analyze !cfgs
      else fun _ -> failwith "no purity analysis calculated when no adce"
    in
    List.iter !cfgs ~f:(fun cfg -> Dead_code_elim.adce cfg purity_fn);
    cfgs := List.map !cfgs ~f:Dead_code_elim.remove_dead_phi_srcs;
  in
  let emit_llvm _ : unit =
    say_if cmd.verbose (fun () -> sprintf "Writing llvm bytecode to %s..." ll_file);
    Out_channel.with_file ll_file ~f:(fun out ->
      Out_channel.fprintf out "%s\n" (Llvm_formatter.format_cfgs !cfgs gdecl_ctxts)) ;
  in
  let emit_bigopt _ : unit =
    if (Emit.(equal cmd.emit LLVM || equal cmd.emit Abstract_assem)) then 
      failwith "Cannot have optimization level above -O1 if emmiting llvm IR";
    llvm_setup () ;
    emit_llvm () ;
    let asm_file = cmd.filename ^ ".s" in
    let llc_cmd =
      sprintf "llc -march=%s -%s %s -o %s"
        (Emit.show cmd.emit) (Opt_level.show cmd.opt_level) ll_file asm_file
    in
    say_if cmd.verbose (fun () -> sprintf "Optimizing with %s" llc_cmd) ;
    let status = Stdlib.Sys.command llc_cmd in
    say_if cmd.verbose (fun () -> sprintf "status = %d" status) ;
    exit 0 ;
  in
    
  (match cmd.opt_level with
  | Opt_level.Opt_none -> if will_use_llvm then llvm_setup ()
  | Opt_level.Opt_one ->
    say_if cmd.verbose (fun () -> "Pre-SSA Optimizations...");

    if not cmd.no_const_copy_prop then 
      cfgs := (List.map ~f:(Constant_copy_prop.cp_basic_blocks ~copy_regs:false) !cfgs);

    if not cmd.no_peephole then List.iter ~f:Peephole.peephole_optimize_cfg !cfgs;

    if not cmd.no_tail_recursion then List.iter !cfgs ~f:Tail_recursion.tail_recursion_optimize;

    let purity_fn =
      if (not cmd.no_ssa) && not cmd.no_adce then 
        Puree_analysis.puree_analyze !cfgs
      else fun _ -> failwith "no purity analysis calculated when no adce"
    in

    if not cmd.no_pre then 
      List.iter !cfgs ~f:Partial_redundancy_elim.eliminate_partial_redundancies;

    if not cmd.no_clean_control then 
      List.iter !cfgs ~f:Dead_code_elim.clean_control_flow;

    if not cmd.no_const_copy_prop then 
      cfgs := List.map ~f:(Constant_copy_prop.cp_basic_blocks ~copy_regs:false) !cfgs;

    if not cmd.no_peephole then List.iter ~f:Peephole.peephole_optimize_cfg !cfgs;

    say_if cmd.dump_pre_ssa (fun () ->
      Cfg_trans.list_cfg_program_to_list !cfgs |> QWT.pp_program);

    if not cmd.no_ssa then (
      say_if cmd.verbose (fun () -> "Translating to SSA...");
      List.iter !cfgs ~f:Ssa_trans.create_ssa;
      say_if cmd.dump_ssa (fun () ->
        Cfg_trans.list_cfg_program_to_list !cfgs |> QWT.pp_program);

    for i = 1 to cmd.ssa_opt_iters do
      say_if cmd.verbose (fun () -> sprintf "SSA optimizations round %d\n" i);
      if not cmd.no_sccp then (
        say_if cmd.verbose (fun () -> "Performing SCCP...");
        cfgs := List.map !cfgs ~f:Scc.scc_optimize;
        say_if cmd.dump_sccp (fun () ->
          Cfg_trans.list_cfg_program_to_list !cfgs |> QWT.pp_program));

      if not cmd.no_global_copy_prop then (
        say_if cmd.verbose (fun () -> "Performing SSA Copy Propagation...");
        cfgs := List.map !cfgs ~f:Ssa_copy_prop.ssa_copy_prop;
        say_if cmd.dump_copy (fun () ->
          Cfg_trans.list_cfg_program_to_list !cfgs |> QWT.pp_program));

      if not cmd.no_adce then (
        say_if cmd.verbose (fun () -> "Performing ADCE...");
        List.iter !cfgs ~f:(fun cfg -> Dead_code_elim.adce cfg purity_fn);
        cfgs := List.map !cfgs ~f:Dead_code_elim.remove_dead_phi_srcs;
        say_if cmd.dump_adce (fun () ->
          Cfg_trans.list_cfg_program_to_list !cfgs |> QWT.pp_program))
    done;

    if not will_use_llvm then (
      say_if cmd.verbose (fun () -> "Destroying SSA...");
      List.iter !cfgs ~f:Ssa_trans.destroy_ssa);
    )
  | Opt_level.Opt_two | Opt_level.Opt_three -> emit_bigopt ()
  );

  if cmd.add_pre_after_ssa then 
    List.iter !cfgs ~f:Partial_redundancy_elim.eliminate_partial_redundancies;

  match cmd.emit with
  (* TODO: How should we deal with the case where it gets here? *)
  | LLVM -> emit_llvm ()
  (* Output: abstract 3-address assem *)
  | Abstract_assem ->
    let file = cmd.filename ^ ".abs" in
    say_if cmd.verbose (fun () -> sprintf "Writing abstract assem to %s..." file);
    Out_channel.with_file file ~f:(fun out ->
      let output_instr instr = Out_channel.fprintf out "\t%s\n" (QWT.format instr) in
      output_instr (QWT.Directive (".file\t\"" ^ cmd.filename ^ "\""));
      output_instr (QWT.Directive ".function\tmain()");
      List.iter ~f:output_instr assem;
      output_instr (QWT.Directive ".ident\t\"15-411 L1 reference compiler\""))
  | ARM_64 ->
    emit_llvm () ;
    let asm_file = cmd.filename ^ ".s" in
    let llc_cmd = sprintf "llc -march=%s -O0 %s -o %s" (Emit.show cmd.emit) ll_file asm_file in
    say_if cmd.verbose (fun () -> sprintf "Outputting arm64 with %s" llc_cmd) ;
    let status = Stdlib.Sys.command llc_cmd in
    say_if cmd.verbose (fun () -> sprintf "status = %d" status) ;
  | X86_64 ->
    say_if cmd.verbose (fun () -> "Adhering to calling conventions...");
    cfgs := List.map ~f:Convention_trans.translate !cfgs;
    (* TODO: Should this be moved up before casing on the output format? *)
    (match cmd.opt_level with
      | Opt_level.Opt_none -> ()
      | Opt_level.Opt_one ->
        if not cmd.no_peephole then List.iter ~f:Peephole.peephole_optimize_cfg !cfgs;
        if not cmd.no_clean_control then List.iter ~f:Dead_code_elim.clean_control_flow !cfgs
      | Opt_level.Opt_two | Opt_level.Opt_three ->
        sprintf "Optimization level %s shouldn't reach here" (Opt_level.show cmd.opt_level)
        |> failwith
    ); 
    say_if cmd.dump_conv (fun () ->
      Cfg_trans.list_cfg_program_to_list !cfgs |> QWT.pp_program);
    let cfgs_x86_div_mod =
      List.map ~f:(Cfg.map_data ~f:Three_addr_trans.div_mod_shift_expansion) !cfgs
    in
    let pre_regalloc_assem =
      List.concat_map ~f:Cfg_trans.list_cfg_to_list cfgs_x86_div_mod
    in
    say_if cmd.dump_pre_regalloc (fun () -> QWT.pp_program pre_regalloc_assem);
    let coalesce =
      Opt_level.(
        match cmd.opt_level with
        | Opt_none -> false
        | Opt_one -> true
        | Opt_two | Opt_three ->
        sprintf "Optimization level %s shouldn't reach here" (Opt_level.show cmd.opt_level)
        |> failwith
      );
    in
    say_if cmd.verbose (fun () -> "Register allocation...");
    let regalloc_assem =
      let base =
        Reg_trans.translate_to_quad_regalloc
          pre_regalloc_assem
          cfgs_x86_div_mod
          ~coalesce
          ~regalloc_cfg:true
      in
      if phys_equal cmd.opt_level Opt_level.Opt_one
      then Peephole.null_sequence_eliminate base
      else base
    in
    say_if cmd.dump_regalloc (fun () ->
      Print_utils.pp_list ~f:QR.format ~sep:"\n" regalloc_assem);
    say_if cmd.verbose (fun () -> "Translating to triple...");
    let x86Assem = Two_addr_trans.x86_gen regalloc_assem in
    let file = cmd.filename ^ ".s" in
    say_if cmd.verbose (fun () -> sprintf "Writing assem to %s..." file);
    Out_channel.with_file file ~f:(fun out ->
      let output_instr instr =
        Out_channel.fprintf out "%s\n" (Assem.X86_Assem.format instr)
      in
      List.iter ~f:output_instr x86Assem);
    say_if cmd.verbose (fun () ->
      sprintf "Total execution time: %fs" (Stdlib.Sys.time ()));
    say_if cmd.verbose Function_timer.pp_segment_timers
;;

let run (cmd : cmd_line_args) : unit =
  try compile cmd with
  | Error_msg.Error ->
    prerr_endline "Compilation failed.";
    exit 1
;;

(* Compiler entry point
 * Use the cmd_line_term to parse the command line arguments, and pass the
 * parsed args to the run function.
 *)
let main () =
  let open Cmdliner in
  let cmd_line_info = Cmd.info "c0c" ~doc:"Compile a c0c source file." in
  let cli_parse_result : cmd_line_args Cmd.t = Cmd.v cmd_line_info cmd_line_term in
  match Cmd.eval_value cli_parse_result with
  | Ok (`Ok cmd_line) -> run cmd_line
  | Ok `Version -> Stdlib.exit Cmd.Exit.ok
  | Ok `Help -> Stdlib.exit Cmd.Exit.ok
  | Error _ -> Stdlib.exit Cmd.Exit.cli_error
;;
