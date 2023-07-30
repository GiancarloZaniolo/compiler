(* This module implements an unoptimal form of purity analysis, where it considers all function 
    calls to automatically be impure

 * Used in ADCE, and can be used to improve PRE
 *)

open Core 

module A = Assem
module QWT = Assem.Quad_With_Temps
module Label = A.Label
module CFG = Cfg
module Symbol_HT = Symbol.Table

(* For future:
  If we wanted to not assume all function calls are impure, we could use Kosaraju's algorithm to 
  find SCCs, then mark all functions with either impure operations or external function calls as 
  impure. We would then know that all functions within an scc must have the same purity, meaning we 
  could coalesce all vertices in SCCs to form a DAG. We could then calculate the reverse 
  dfs traversal, and assign purity by propagating purity down the tree, where anything that isnt 
  impure is pure  *)

let puree_analyze (cfgs:  QWT.program CFG.t list) : ( Symbol.t -> bool ) = 
  let puree_tbl = Symbol_HT.create () in
  let rec puree_analyze_rec cfgs = (match cfgs with
    | cfg :: rest -> 
      let all_lbl = CFG.get_all_labels cfg in
      let rec analyze_cfg labels = (match labels with
        | label :: rest -> 
          let all_instrs = CFG.get_data_exn cfg ~label in
          let rec analyze_instrs instrs = 
            let check_impure_error_label l = (match l with
              | Label.MEM_LABEL | Label.ARITH_LABEL -> false
              | Label.Fn_label _ | Label.ENTRY_LABEL | Label.EXIT_LABEL | Label.Local_label _ 
                -> true) in
            (match instrs with
            | instr :: rest -> (match instr with
              | QWT.Unop _ | QWT.Mov _ | QWT.Phi _ | QWT.Label _ | QWT.Mem_read _
              | QWT.Return _ | QWT.Directive _ | QWT.Comment _ -> analyze_instrs rest
              | QWT.Call _ | QWT.Mem_write _ -> false
              | QWT.Goto g -> if check_impure_error_label g then analyze_instrs rest else false
              | QWT.Binop b -> (match b.op with
                | A.Div | A.Mod -> false
                | A.Add | A.Sub | A.Mul | A.LShift | A.RShift | A.RShift_unsigned | A.BWXor | A.BWAnd 
                | A.BWOr -> analyze_instrs rest)
                | QWT.If i -> 
                  if (check_impure_error_label i.if_true) && (check_impure_error_label i.if_false) 
                    then analyze_instrs rest else false)

            | [] -> true) in

          if analyze_instrs all_instrs then
            analyze_cfg rest
          else 
            false
        | [] -> true ) in

      let fn_label = (match CFG.succs cfg Label.ENTRY_LABEL with
        | [Label.Fn_label fn] -> fn.name
        | _ -> failwith "Expected function label as child of entry") in
      Symbol_HT.add_exn puree_tbl ~key:fn_label ~data:(analyze_cfg all_lbl);
      puree_analyze_rec rest

    | [] -> ()) in

  puree_analyze_rec cfgs;
  (fun sym -> match Symbol_HT.find puree_tbl sym with
    | Some b -> b
    | None -> false)
  
  