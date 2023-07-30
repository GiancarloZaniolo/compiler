(* Module which translates QWT which already complies with LLVM IR's SSA requirements into LLVM IR *)

open Core

module A = Assem
module AL = Assem.Label
module QWT = Assem.Quad_With_Temps
module CFG = Cfg
module STIR = A.Stack_Temp_Imm_Reg
module L_HS = Assem.Label.Hash_set
module QWT_HT = Assem.Quad_With_Temps.Operand_hashtbl
module TC = Typechecker

let tc_opsize = function
  | Ast.Int | Ast.Bool -> A.S_32
  | Ast.Ptr _ | Ast.Arr _ -> A.S_64
  | Ast.Struct _ -> failwith "Does not expect function to return a large type"
  | Ast.Any_type -> failwith "Does not expect function to return Any_type" 
  | Ast.Type_ident _ -> failwith "Does not expect typedefs at this poitn"

let populate_mem_arith (cfg : QWT.program CFG.t) : unit =
  let populate label =
    let int_code = AL.lbl_to_int label |> Int32.of_int_exn |> STIR.Imm32 in
    let int_code_temp : A.sized_temp = { size = A.S_32 ; temp = Temp.create () } in
    let int_code_stir = STIR.Temp int_code_temp in
    let instrs =
      [ QWT.Label label
      ; QWT.Mov { src = int_code ; dest = int_code_stir }
      ; QWT.Call { dest = None ; fn_label = { name = Symbol.symbol "raise" ; param_temps = [ int_code_temp ] ; ret_size_opt = None } }
      ; QWT.Goto label ]
    in
    CFG.set_data cfg ~label ~data:instrs
  in
  populate AL.ARITH_LABEL ;
  populate AL.MEM_LABEL


let format_qwt_binop = function
  | A.Add -> "add"
  | A.Sub -> "sub"
  | A.Mul -> "mul"
  | A.Div -> "sdiv"
  | A.Mod -> "srem"
  | A.LShift -> "shl"
  | A.RShift -> "ashr"
  | A.RShift_unsigned -> "lshr"
  | A.BWAnd -> "and"
  | A.BWOr -> "or"
  | A.BWXor -> "xor"

let format_qwt_comp_binop_signed = function
  | A.LessThan -> "slt"
  | A.LessThanEq -> "sle"
  | A.GreaterThan -> "sgt"
  | A.GreaterThanEq -> "sge"
  | A.EqualsTo -> "eq"
  | A.NotEqualsTo -> "ne"

let format_qwt_comp_binop_unsigned = function
  | A.LessThan -> "ult"
  | A.LessThanEq -> "ule"
  | A.GreaterThan -> "ugt"
  | A.GreaterThanEq -> "uge"
  | A.EqualsTo -> "eq"
  | A.NotEqualsTo -> "ne"

let get_stir_size = function
  | STIR.Imm32 _ -> A.S_32
  | STIR.Imm64 _ -> A.S_64
  | STIR.Temp t -> t.size
  | STIR.Reg r -> r.size
  | STIR.Arg_In_Stack_Idx i -> i.size
  | STIR.Arg_Out_Stack_Idx i -> i.size
  (* This may be wrong, but not sure how we would case given the operand *)
  | STIR.Addr_mode _ -> A.S_64


let fn_to_entry_lbl fn_sym = sprintf "entry_%s" (Symbol.name fn_sym)
let format_label = function 
  | AL.ARITH_LABEL -> "ARITH"
  | AL.MEM_LABEL -> "MEM"
  | AL.ENTRY_LABEL -> "ENTRY"
  | AL.EXIT_LABEL -> "EXIT"
  | AL.Fn_label f -> fn_to_entry_lbl f.name
  | AL.Local_label l -> (Local_label.name l)

let format_size = function
  | A.S_32 -> "i32" 
  | A.S_64 -> "i64"

let format_stir_size stir = 
  format_size (get_stir_size stir)

let rec format_stir stir = 
  (match stir with
  | STIR.Imm32 i -> Int32.to_string i
  | STIR.Imm64 i -> Int64.to_string i
  | STIR.Reg _ -> failwith "There should be no predefined registers in llvm trans"
  | STIR.Temp t -> sprintf "%s" (Temp.name t.temp)
  | STIR.Arg_In_Stack_Idx _ -> failwith "There should be no predefined stack indices in llvm trans"
  | STIR.Arg_Out_Stack_Idx _ -> failwith "There should be no predefined stack indices in llvm trans"
  | STIR.Addr_mode _ -> failwith "Addr_mode should be unrolled")

and preformat_stir stir = 
  (match stir with
  | STIR.Addr_mode a -> 
    let make_stir_64 t = STIR.Temp { temp = t ; size = A.S_64 } in 
    let t1 = make_stir_64 (Temp.create ()) in 
    let t2 = make_stir_64 (Temp.create ()) in 
    let t3 = make_stir_64 (Temp.create ()) in
    let addr_mode_unroll_instrs = 
      sprintf 
        "%s\n%s\n%s" 
        (format_instr
          (QWT.Binop 
            { op = A.Mul ; dest = t1 
            ; lhs = STIR.Temp a.index
            ; rhs = STIR.Imm64 (A.addr_mode_scale_to_int64 a.scale) })) 
        (format_instr
          (QWT.Binop 
            { op = A.Add 
            ; dest = t2 
            ; lhs = STIR.Temp a.base 
            ; rhs = t1 }))
        (format_instr
          (QWT.Binop 
            { op = A.Add 
            ; dest = t3 
            ; lhs = STIR.Imm64 (Int64.of_int32 a.disp) 
            ; rhs = t2 }))
    in
    (t3,addr_mode_unroll_instrs)
  | STIR.Imm32 _ | STIR.Imm64 _ | STIR.Reg _ | STIR.Temp _ | STIR.Arg_In_Stack_Idx _ 
  | STIR.Arg_Out_Stack_Idx _ -> (stir,""))

and format_instr (instr : QWT.instr) : string =
  let format_param (p : A.sized_temp) = sprintf  "%s %s" (format_size p.size) (Temp.name p.temp) in
  (match instr with
  | Binop b -> 
    let (prelhs,prelhs_str) = preformat_stir b.lhs in
    let (prerhs,prerhs_str) = preformat_stir b.rhs in
    sprintf 
      "%s%s%s = %s %s %s, %s"
      prelhs_str prerhs_str (format_stir b.dest) (format_qwt_binop b.op) (format_stir_size b.dest) 
      (format_stir prelhs) (format_stir prerhs)
  | Unop u -> 
    (match u.op with
    | A.LEA -> 
      let (presrc,presrc_str) = preformat_stir u.src in
      sprintf  
        "%s\n%s" 
        presrc_str 
        (format_instr (QWT.Mov { dest = u.dest ; src = presrc}))
    | A.MOVSXD -> (* Hopefully we never have an addressing mode as an operand here *)
      sprintf "%s = sext i32 %s to i64" (format_stir u.dest) (format_stir u.src)
    | A.CDQ -> failwith "CQD should not be present in llvm translation")
  | Mov m -> (*assumes there will never be an addressing mode on a mov instruction*)
    sprintf
      "%s = bitcast %s %s to %s" 
      (format_stir m.dest)
      (format_stir_size m.dest)
      (format_stir m.src)
      (format_stir_size m.dest)
  | Phi p -> 
    let fold_one_src ~key ~data acc = Hash_set.fold ~init:acc ~f:(fun acc pred -> (key,pred) :: acc) data in
    let pair_list = QWT_HT.fold ~init:[] ~f:fold_one_src p.srcs in
    let format_pair (src, pred) =
      sprintf "[ %s, %%%s ]" (format_stir src) (format_label pred) in
      sprintf
        "%s = phi %s %s"
        (format_stir p.dest)
        (format_stir_size p.dest)
        (Print_utils.pp_list ~f:format_pair ~sep:", " pair_list)
  | If i -> (*assumes there will never be an addressing mode on an if instruction*)
    let t_dest = Temp.create () in
    let lhs_size =  (match get_stir_size i.lhs with 
      | A.S_32 -> format_qwt_comp_binop_signed i.op 
      | A.S_64 -> format_qwt_comp_binop_unsigned i.op) in
    sprintf 
      "%s = icmp %s %s %s, %s\nbr i1 %s, label %%%s, label %%%s"
      (Temp.name t_dest)
      lhs_size
      (format_stir_size i.lhs)
      (format_stir i.lhs)
      (format_stir i.rhs)
      (Temp.name t_dest)
      (format_label i.if_true)
      (format_label i.if_false)
  | Call c -> 
    (match c.dest with
    | Some dest -> 
      sprintf 
        "%s = call %s @%s (%s)" 
        (Temp.name dest.temp)
        (format_size dest.size)
        (Symbol.name c.fn_label.name)
        (Print_utils.pp_list ~f:format_param ~sep:", " c.fn_label.param_temps)
    | None ->
      sprintf 
      "call void @%s (%s)" 
      (Symbol.name c.fn_label.name)
      (Print_utils.pp_list ~f:format_param ~sep:", " c.fn_label.param_temps))
  | Goto g -> sprintf "br label %%%s" (format_label g)
  | Label l -> 
    (match l with
    | AL.Fn_label f ->
      let fn_start_str =
        (match f.ret_size_opt with
        | Some r -> 
          sprintf
            "define %s @%s (%s) {"
            (format_size r)
            (Symbol.name f.name)
            (Print_utils.pp_list ~f:format_param ~sep:", " f.param_temps)
        | None ->
          sprintf
            "define void @%s (%s) {"
            (Symbol.name f.name)
            (Print_utils.pp_list ~f:format_param ~sep:", " f.param_temps))
      in
      sprintf "%s\ndummy_%s:\nbr label %%%s\n%s:"
        fn_start_str (format_label l) (format_label l) (format_label l)
    | _ -> (format_label l) ^ ":")
  | Return r -> (match r with
    | Some r -> sprintf "ret %s %s" (format_stir_size r) (format_stir r)
    | None -> "ret void")
  | Mem_read m -> 
    let src_ptr = STIR.Temp { temp = Temp.create () ; size = A.S_64 } in
    let inttoptr =
      sprintf "%s = inttoptr %s %s to %s*"
        (format_stir src_ptr)
        (format_stir_size m.src)
        (format_stir m.src)
        (format_stir_size m.dest)
    in
    let load =
      sprintf
        "%s = load %s, %s* %s"
        (format_stir m.dest)
        (format_stir_size m.dest)
        (format_stir_size m.dest)
        (format_stir src_ptr)
    in
    sprintf "%s\n%s" inttoptr load
  | Mem_write m -> 
    let dest_ptr = STIR.Temp { temp = Temp.create () ; size = A.S_64 } in
    let inttoptr =
      sprintf "%s = inttoptr %s %s to %s*"
        (format_stir dest_ptr)
        (format_stir_size m.dest)
        (format_stir m.dest)
        (format_stir_size m.src)
    in
    let store =
      sprintf
        "store %s %s, %s* %s"
        (format_stir_size m.src)
        (format_stir m.src)
        (format_stir_size m.src)
        (format_stir dest_ptr)
    in
    sprintf "%s\n%s" inttoptr store
  | Directive _ -> "" (*Directives shouldn't be used for anything, and if so, is x86 code*)
  | Comment _ -> "")



let format_cfg (cfg : QWT.program CFG.t) : string =
  let format (prog : QWT.program) : string list =
    [ List.map prog ~f:format_instr |> String.concat ~sep:"\n" ]
  in
  populate_mem_arith cfg ;
  let fun_str =
    CFG.map_data ~f:format cfg
    |> Cfg_trans.list_cfg_to_list
    |> String.concat ~sep:"\n"
  in
  fun_str ^ "\n}"

let define_external ~key ~(data : TC.fdecl_status) acc = 
  let format_param_def (tc_type_ident : Ast.type_ident) = 
    tc_opsize tc_type_ident.type_ |> format_size in
  if data.fdecl.extern then
    let acc' = (match data.fdecl.ret_type with
    | Some s -> 
      sprintf
        "declare %s @%s (%s)\n"
        (format_size (tc_opsize s))
        (Symbol.name key)
        (Print_utils.pp_list ~f:format_param_def ~sep:", " data.fdecl.param_list)
    | None ->
      sprintf
        "declare void @%s (%s)\n"
        (Symbol.name key)
        (Print_utils.pp_list ~f:format_param_def ~sep:", " data.fdecl.param_list)) in
      acc' ^ acc
  else
    acc

let format_cfgs (cfgs : QWT.program CFG.t list) (gdecl_ctxts : TC.gdecl_ctxts) : string =
  let pre_decs =
    [ "declare void @raise (i32)"
    ; "declare void @abort ()"
    ; "declare i64 @calloc (i64, i64)"
    ]
  in
  let init = String.concat pre_decs ~sep:"\n" in
  let ext_decls = TC.SHT.fold gdecl_ctxts.fdecl_ctxt ~init ~f:define_external in
  List.fold_left cfgs ~init:ext_decls  ~f:(fun acc cfg -> acc ^ (format_cfg cfg))