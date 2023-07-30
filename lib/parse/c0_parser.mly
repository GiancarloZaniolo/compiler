%{
(* L4 Compiler
 * L4 grammar
 * Author: Kaustuv Chaudhuri <kaustuv+@cs.cmu.edu>
 * Modified: Frank Pfenning <fp@cs.cmu.edu>
 *
 * Modified: Anand Subramanian <asubrama@andrew.cmu.edu> Fall 2010
 * Now conforms to the L1 fragment of C0
 *
 * Modified: Maxime Serrano <mserrano@andrew.cmu.edu> Fall 2014
 * Should be more up-to-date with 2014 spec
 *
 * Modified: Alice Rao <alrao@andrew.cmu.edu> Fall 2017
 *   - Update to use Core instead of Core.Std and ppx
 *
 * Modified: Nick Roberts <nroberts@alumni.cmu.edu>
 *   - Update to use menhir instead of ocamlyacc.
 *   - Improve presentation of marked asts.
 *
 * Modified: Giancarlo Zaniolo (gzaniolo)
 * Modified: Elan Biswas (elanb)
 *
 * Converted to OCaml by Michael Duggan <md5i@cs.cmu.edu>
 *)

let mark
  (data : 'a)
  (start_pos : Lexing.position)
  (end_pos : Lexing.position) : 'a Mark.t =
  let src_span = Mark.of_positions start_pos end_pos in
  Mark.mark data src_span

%}

%token Eof
%token Semicolon
%token Comma
%token Dot
%token R_arrow
%token <Int32.t> Dec_const
%token <Int32.t> Hex_const
%token <Symbol.t> Ident
%token <Symbol.t> Type_ident
%token True False
%token Null Alloc Alloc_array
%token Return
%token Int Bool Void Struct
%token<Symbol.t * Pst.type_> Typedef
%token Assert
%token Plus Minus Star Slash Percent LShift RShift
%token Assign Plus_eq Minus_eq Star_eq Slash_eq Percent_eq 
%token BitwiseAnd_eq BitwiseXor_eq BitwiseOr_eq LShift_eq RShift_eq
%token LessThan LessThanEq GreaterThan GreaterThanEq EqualsTo NotEqualsTo
%token And Or
%token BitwiseAnd BitwiseXor BitwiseOr
%token Question Colon
%token Bang
%token BitwiseNot
%token If Else While For
%token L_brace R_brace
%token L_paren R_paren
%token L_brack R_brack
%token Unary
%token Minus_minus Plus_plus

(* Unary and No_Else are dummy terminals.
 * We need dummy terminals if we wish to assign a precedence
 * to a production that does not correspond to the precedence of
 * the rightmost terminal in that production.
 * Implicit in this is that precedence can only be inferred for
 * terminals. Therefore, don't try to assign precedence to "rules"
 * or "productions".
 *)
%nonassoc No_Else
%nonassoc Else
%right Question Colon
%left Or
%left And
%left BitwiseOr
%left BitwiseXor
%left BitwiseAnd
%left EqualsTo NotEqualsTo
%left LessThan LessThanEq GreaterThan GreaterThanEq
%left RShift LShift
%left Plus Minus
%left Star Slash Percent
%right Unary
%nonassoc L_brack R_arrow Dot

%start program

(* It's only necessary to provide the type of the start rule,
 * but it can improve the quality of parser type errors to annotate
 * the types of other rules.
 *)
%type <Pst.program> program
%type <Pst.gdecl> gdecl
%type <Pst.mgdecl> m(gdecl)
%type <Pst.fdecl> fdecl
%type <Pst.fdefn> fdefn
%type <Pst.sdefn> sdefn
%type <Pst.sdecl> sdecl
%type <Symbol.t> normal_or_type_ident
%type <Symbol.t> struct_name
(* We do not have a separate rule for param here because it would be the same as type_ident *)
(* However, we need a rule for fields because of the semicolon after the ident *)
%type <Pst.type_ident> field
%type <Pst.type_ident list> field_list
%type <Pst.type_ident> param 
%type <Pst.type_ident list> param_list_follow
%type <Pst.type_ident list> param_list
%type <Pst.mexp list> arg_list_follow
%type <Pst.mexp list> arg_list
%type <Pst.typedef> typedef
%type <Pst.ret_type> ret_type
%type <Pst.mstm list> block
%type <Pst.mstm list> stms
%type <Pst.stm> stm
%type <Pst.mstm> m(stm)
%type <Pst.decl> decl
%type <Pst.simp> simp
%type <Pst.simp Mark.t> m(simp)
%type <Pst.simp Mark.t option> msimpopt
%type <Pst.control> control
(* We have this additional rule so that we can explicitly disallow *x++ without ambiguity *)
%type <Pst.exp> exp_without_star
%type <Pst.mexp> m(exp_without_star)
%type <Pst.exp> exp
%type <Pst.mexp> m(exp)
%type <Core.Int32.t> int_const
%type <Pst.binop> binop
%type <Pst.unop> unop
%type <Pst.type_> type_
%type <Pst.asop> asnop
%type <Pst.asop> postop

%%

program :
  | Eof
      { let p : Pst.program = [] in p }
  | g = m(gdecl); gs = program;
      { let p : Pst.program = g :: gs in p }
  ;

gdecl :
  | fdecl = fdecl
      { Pst.Fdecl fdecl }
  | fdefn = fdefn
      { Pst.Fdefn fdefn }
  | typedef = typedef
      { Pst.Typedef typedef }
  | sdefn = sdefn
      { Pst.Sdefn sdefn }
  | sdecl = sdecl
      { Pst.Sdecl sdecl }
  ;

fdecl :
  | ret_type = ret_type; ident = Ident; param_list = param_list; Semicolon;
      { { ret_type ; ident ; param_list ; extern = false } }
  ;

fdefn :
  | ret_type = ret_type; ident = Ident; param_list = param_list; block = block;
      { { ret_type ; ident ; param_list ; block } }
  ;

sdecl :
  | ident = struct_name ; Semicolon ;
      { ident }

sdefn :
  | ident = struct_name ; L_brace ;
    field_list = field_list ; R_brace ; Semicolon ;
      { let s : Pst.sdefn = { ident ; field_list } in s }

(* In some places a name is allowed to overlap with a typedef. The lexer emits a different token for
   idents that have been type defined. Rather than casing in the lexer and emitting a regular ident
   in these cases, it is easier just to catch it in the parser. *)
normal_or_type_ident :
  | ident = Ident ;
        { ident }
  | ident = Type_ident ;
        { ident }

struct_name :
  | Struct ;
    ident = normal_or_type_ident ;
        { ident }

param :
  | type_ = type_; ident = Ident;
      { let ti : Pst.type_ident = { type_ ; ident } in ti }
  ;

field :
  | type_ = type_ ; ident = normal_or_type_ident ; Semicolon;
      { let ti : Pst.type_ident = { type_ ; ident } in ti }

field_list :
  | (* empty *)
      { [] }
  | field = field; fields = field_list;
      { field :: fields }

param_list_follow :
  | (* empty *)
      { [] }
  | Comma; param = param ; params = param_list_follow;
      { param :: params }
  ;

param_list :
  | L_paren; R_paren;
      { [] }
  | L_paren; param = param; params = param_list_follow; R_paren;
      { param :: params }
  ;

typedef :
  | ident_type = Typedef ; Semicolon ;
      { let (ident, type_) = ident_type in
        let tdef : Pst.typedef = { type_ ; ident }
        in tdef
      }
  ;

type_ :
  | Int;
      { Pst.Int }
  | Bool;
      { Pst.Bool }
  | ident = Type_ident;
      { Pst.Type_ident ident }
  | ident = struct_name;
      { Pst.Struct ident }
  | type_ = type_ ; Star ;
      { Pst.Ptr type_ }
  | type_ = type_ ; L_brack ; R_brack ;
      { Pst.Arr type_ }
  ;

ret_type :
  | type_ = type_;
      { Pst.Type type_ }
  | Void;
      { Pst.Void }
  ;

block :
  | L_brace; stms = stms; R_brace;
      { stms }
  ;

decl :
| t = type_; ident = Ident;
    { Pst.New_var { typ = t; sym = ident; } }
| t = type_; ident = Ident; Assign; e = m(exp);
    { Pst.Init { typ = t; sym = ident; exp = e; } }
;

(* This higher-order rule produces a marked result of whatever the
 * rule passed as argument will produce.
 *)
m(x) :
  | x = x;
      (* $startpos(s) and $endpos(s) are menhir's replacements for
       * Parsing.symbol_start_pos and Parsing.symbol_end_pos, but,
       * unfortunately, they can only be called from productions. *)
      { mark x $startpos(x) $endpos(x) }
  ;

stms : 
  | (* empty *)
      { [] }
  | hd = m(stm); tl = stms;
      { hd :: tl }
  ;

stm :
  | s = simp; Semicolon;
      { Pst.Simp s }
  | c = control;
      { Pst.Control c }
  | body = block;
      { Pst.Block body }
  ;

simp :
  | Star ; e = exp ; p = postop ;
      { let _ : Pst.exp = e in let _ : Pst.asop = p in Pst.PARSE_FAIL } 
  | lval = m(exp); (* this is to avoid ambiguity in grammar, originally m(lvalue) *)
    asop = asnop;
    mexp = m(exp);
      { Pst.Assign { lval ; asop ; mexp } }
  (* Want to avoid 2 ambiguities in grammar:
     (1) the lvalue problem and (2) explicit disallowing of *x++/-- *)
  | lval = m(exp_without_star); 
    asop = postop;
      (* Elaborate d++/d-- into d += 1/d -= 1 *)
      { Pst.Assign { lval ; asop ; mexp = Int32.of_int 1 |> Pst.Const |> Mark.naked }
}
  | d = decl;
      { Pst.Declare d}
  | e = m(exp);
      { Pst.Exp e}
  ;

msimpopt :
  | s = m(simp)
      { Some s }
  | (* empty *)
      { None }
  ;

control :
  | If; L_paren; e = m(exp); R_paren;
    if_true = m(stm);
    Else;
    otherwise = m(stm);
      { Pst.If { cond = e; body = if_true; els = Some otherwise; } }
  | If; L_paren; e = m(exp); R_paren;
    if_true = m(stm); %prec No_Else
      { Pst.If { cond = e; body = if_true; els = None; } }
  | While; L_paren; e = m(exp); R_paren;
    s = m(stm);
      { Pst.While { guard = e; body = s; } }
  | For; L_paren; s1 = msimpopt; Semicolon;
    e = m(exp); Semicolon;
    s2 = msimpopt; R_paren;
    s = m(stm);
      { let to_mstm = Option.map (Mark.map ~f:(fun simp -> Pst.Simp simp)) in
        Pst.For { simp1 = to_mstm s1; guard = e; simp2 = to_mstm s2; body = s } }
  | Assert; L_paren; mexp = m(exp); R_paren; Semicolon;
      { Pst.Assert mexp }
  | Return; Semicolon;
      { Pst.Return None }
  | Return; e = m(exp); Semicolon;
      { Pst.Return (Some e) }
  ;

arg_list_follow :
  | (* empty *)
      { [] }
  | Comma; mexp = m(exp); mexps = arg_list_follow;
      { mexp :: mexps }
  ;

arg_list :
  | L_paren; R_paren;
      { [] }
  | L_paren; mexp = m(exp); mexps = arg_list_follow; R_paren;
      { mexp :: mexps }
  ;

exp_without_star :
  | L_paren; e = exp; R_paren;
      { e }
  | c = int_const;
      { Pst.Const c }
  | True;
      { Pst.True }
  | False;
      { Pst.False }
  | Null;
      { Pst.Null }
  | ident = Ident;
      { Pst.Var ident }
  | lhs = m(exp);
    op = binop;
    rhs = m(exp);
      { Pst.Binop { op; lhs; rhs; } }
  | u = unop; e = m(exp); %prec Unary
      { Pst.Unop { op = u; operand = e; } }
  | c = m(exp); Question; t = m(exp); Colon; f = m(exp);
      { Pst.Ternary { cond = c; if_true = t; if_false = f; } }
  | ident = Ident; arg_list = arg_list;
      { Pst.Fn_Call { ident ; arg_list } }
  | struct_ = m(exp); Dot;
    field = normal_or_type_ident;
      { Pst.Field_acc { struct_ ; field } }
  | struct_ = m(exp); R_arrow;
    field = normal_or_type_ident;
      { Pst.Field_dref { struct_ ; field } }
  | Alloc ; L_paren ;
    type_ = type_ ; R_paren ;
      { Pst.Alloc type_ }
  | Alloc_array ; L_paren ;
    type_ = type_ ; Comma ;
    size = m(exp) ; R_paren ;
      { Pst.Alloc_array { type_ ; size } }
  | arr = m(exp); L_brack;
    index = m(exp); R_brack;
      { Pst.Arr_acc { arr ; index }}
  ;

exp :
  | e = exp_without_star ;
      { e }
  | Star ; mexp = m(exp) ;
      { Pst.Pointer_dref mexp }
  ;

int_const :
  | c = Dec_const;
      { c }
  | c = Hex_const;
      { c }
  ;

asnop :
  | Assign
      { Pst.AEquals }
  | Plus_eq
      { Pst.APlus }
  | Minus_eq
      { Pst.AMinus }
  | Star_eq
      { Pst.ATimes }
  | Slash_eq
      { Pst.ADivided_by }
  | Percent_eq
      { Pst.AModulo }
  | BitwiseAnd_eq
      { Pst.ABWAnd }
  | BitwiseXor_eq
      { Pst.ABWXor }
  | BitwiseOr_eq
      { Pst.ABWOr }
  | LShift_eq
      { Pst.ALShift }
  | RShift_eq
      { Pst.ARShift }
  ;

(* See the menhir documentation for %inline.
 * This allows us to factor out binary operators while still
 * having the correct precedence for binary operator expressions.
 *)
%inline
binop :
  | Plus;
      { Pst.Plus }
  | Minus;
      { Pst.Minus }
  | Star;
      { Pst.Times }
  | Slash;
      { Pst.Divided_by }
  | Percent;
      { Pst.Modulo }
  | LessThan
      { Pst.LessThan }
  | LessThanEq
      { Pst.LessThanEq }
  | GreaterThan
      { Pst.GreaterThan }
  | GreaterThanEq
      { Pst.GreaterThanEq }
  | EqualsTo
      { Pst.EqualsTo }
  | NotEqualsTo
      { Pst.NotEqualsTo }
  | And
      { Pst.And }
  | Or
      { Pst.Or }
  | BitwiseAnd
      { Pst.BitwiseAnd }
  | BitwiseXor
      { Pst.BitwiseXor }
  | BitwiseOr
      { Pst.BitwiseOr }
  | LShift
      { Pst.LShift }
  | RShift
      { Pst.RShift }
  ;

unop :
  | Minus; 
      { Pst.Negative }
  | BitwiseNot;
      { Pst.BitwiseNot }
  | Bang;
      { Pst.Bang }
  ;

postop :
  | Plus_plus;
      { Pst.APlus }
  | Minus_minus;
      { Pst.AMinus }
  ;


%%
