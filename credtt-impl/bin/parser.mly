%{
open Credtt_lib.Raw
%}

%token <string> IDENT
%token <string> OPERATOR
%token <int> NUM
%token MODULE WHERE OPEN IMPORT USING DATA RECORD FIELD
%token LET IN CASE OF WITH
%token INFIX INFIXL INFIXR
%token FORALL SET PROP REFL FST SND INL INR
%token POSTULATE DERIVE FROM BY CONTRADICT CONCLUDE NEGATE
%token PROVABLE FIXPOINT ENCODE
%token STABLE UNSTABLE
%token SUP WINF
%token AT
%token LAMBDA ARROW DARROW TIMES PLUS EQ COLON SEMI COMMA DOT BAR SLASH
%token LWEIGHT RWEIGHT
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET UNDERSCORE
%token TOP BOT CDOT NEG EQUIV LEQ TURNSTILE TYCOLON SIGMA PI EPSILON
%token BBZERO BBONE
%token EOF

%start <Credtt_lib.Raw.program> program

%%

program:
  | ds = separated_list(SEMI, decl) EOF { ds }

decl:
  (* Type signature: name : type @ credence *)
  | name = IDENT COLON ty = ty c = credence_annotation
    { DSig (name, ty, c) }

  (* Definition with patterns: name pat1 pat2 = term *)
  | name = IDENT pats = list(pattern_atom) EQ body = term
    { DDef (name, pats, body) }

  (* Definition with where clause *)
  | name = IDENT pats = list(pattern_atom) EQ body = term WHERE local = where_block
    { DDef (name, pats, TWhere (body, local)) }

  (* Data declaration *)
  | DATA name = IDENT tele = telescope WHERE constrs = list(constructor)
    { DData (name, tele, constrs) }

  (* Record declaration *)
  | RECORD name = IDENT tele = telescope WHERE FIELD fields = list(field_decl)
    { DRecord (name, tele, fields) }

  (* Module declaration *)
  | MODULE name = qualified_name WHERE ds = indented_block
    { DModule (String.concat "." name, ds) }

  (* Open import *)
  | OPEN IMPORT path = qualified_name
    { DImport (path, None) }
  | OPEN IMPORT path = qualified_name USING LPAREN names = separated_list(SEMI, IDENT) RPAREN
    { DImport (path, Some names) }

  (* Open module *)
  | OPEN name = IDENT
    { DOpen (name, None) }
  | OPEN name = IDENT USING LPAREN names = separated_list(SEMI, IDENT) RPAREN
    { DOpen (name, Some names) }

  (* Fixity declarations *)
  | INFIX n = NUM op = operator_name
    { DInfix (ANone, n, op) }
  | INFIXL n = NUM op = operator_name
    { DInfix (ALeft, n, op) }
  | INFIXR n = NUM op = operator_name
    { DInfix (ARight, n, op) }

  (* Proof declarations - @ notation (preferred) *)
  | POSTULATE name = IDENT COLON prop = IDENT AT c = credence
    { DPostulate (name, prop, c) }

  | DERIVE name = IDENT COLON prop = IDENT AT c = credence FROM from_name = IDENT BY by_name = justification
    { DDerive (name, prop, c, from_name, by_name) }

  (* Proof declarations - bracket notation (legacy, kept for compatibility) *)
  | POSTULATE name = IDENT COLON prop = IDENT LBRACKET c = credence RBRACKET
    { DPostulate (name, prop, c) }

  | DERIVE name = IDENT COLON prop = IDENT LBRACKET c = credence RBRACKET FROM from_name = IDENT BY by_name = justification
    { DDerive (name, prop, c, from_name, by_name) }

  (* Proof declarations - unicode bracket notation (kept for compatibility) *)
  | POSTULATE name = IDENT COLON prop = IDENT LWEIGHT c = credence RWEIGHT
    { DPostulate (name, prop, c) }

  | DERIVE name = IDENT COLON prop = IDENT LWEIGHT c = credence RWEIGHT FROM from_name = IDENT BY by_name = justification
    { DDerive (name, prop, c, from_name, by_name) }

  | CONTRADICT p = IDENT q = IDENT
    { DContradict (p, q) }

  | CONCLUDE name = IDENT FROM from_name = IDENT
    { DConclude (name, from_name) }

  | NEGATE name = IDENT FROM from_name = IDENT
    { DConclude (name, from_name) }

  (* Stability assertions *)
  | STABLE name = IDENT
    { DStable name }

  | UNSTABLE name = IDENT
    { DUnstable name }

  (* Meta-theory declarations - @ notation (preferred) *)
  | PROVABLE name = IDENT COLON prop = IDENT AT c = credence
    { DProvable (name, prop, c) }

  (* Meta-theory declarations - bracket notation (legacy) *)
  | PROVABLE name = IDENT COLON prop = IDENT LBRACKET c = credence RBRACKET
    { DProvable (name, prop, c) }

  (* Meta-theory declarations - unicode bracket notation *)
  | PROVABLE name = IDENT COLON prop = IDENT LWEIGHT c = credence RWEIGHT
    { DProvable (name, prop, c) }

  | FIXPOINT name = IDENT EQ c = credence
    { DFixpoint (name, c) }

  | ENCODE name = IDENT EQ prop = IDENT
    { DEncode (name, prop) }

qualified_name:
  | parts = separated_nonempty_list(DOT, IDENT) { parts }

operator_name:
  | IDENT { $1 }
  | OPERATOR { $1 }

(* Justification names for derive statements - includes keywords that can be used as justifications *)
justification:
  | IDENT { $1 }
  | NEGATE { "negate" }
  | STABLE { "stable" }
  | UNSTABLE { "unstable" }

where_block:
  | ds = indented_block { ds }
  | LBRACE ds = separated_list(SEMI, decl) RBRACE { ds }

indented_block:
  | ds = list(decl) { ds }

constructor:
  | name = IDENT COLON ty = ty { (name, ty) }

field_decl:
  | name = IDENT COLON ty = ty { (name, ty) }

telescope:
  | bindings = list(tele_binding) { List.flatten bindings }

tele_binding:
  (* Explicit: (x : A) *)
  | LPAREN names = nonempty_list(IDENT) COLON ty = ty RPAREN
    { List.map (fun n -> (n, Explicit, ty)) names }
  (* Implicit: {x : A} *)
  | LBRACE names = nonempty_list(IDENT) COLON ty = ty RBRACE
    { List.map (fun n -> (n, Implicit, ty)) names }
  (* Implicit without type: {x} *)
  | LBRACE names = nonempty_list(IDENT) RBRACE
    { List.map (fun n -> (n, Implicit, TyVar "_")) names }

(* Types *)
ty:
  | t = ty_arrow { t }

ty_arrow:
  | t = ty_sum { t }
  (* Dependent function: (x : A) -> B or {x : A} -> B *)
  | LPAREN x = IDENT COLON a = ty RPAREN ARROW b = ty_arrow
    { TyPi (x, Explicit, a, b) }
  | LBRACE x = IDENT COLON a = ty RBRACE ARROW b = ty_arrow
    { TyPi (x, Implicit, a, b) }
  | LBRACE x = IDENT RBRACE ARROW b = ty_arrow
    { TyPi (x, Implicit, TyVar "_", b) }
  (* Forall *)
  | FORALL bindings = nonempty_list(tele_binding) ARROW b = ty_arrow
    { List.fold_right (fun (n, i, t) acc -> TyPi (n, i, t, acc)) (List.flatten bindings) b }
  (* Non-dependent function *)
  | a = ty_sum ARROW b = ty_arrow
    { TyArrow (a, b) }

ty_sum:
  | t = ty_product { t }
  | a = ty_sum PLUS b = ty_product { TySum (a, b) }

ty_product:
  | t = ty_app { t }
  (* Dependent pair: Sigma (x : A) B or (x : A) * B *)
  | SIGMA LPAREN x = IDENT COLON a = ty RPAREN b = ty_product
    { TySigma (x, a, b) }
  | LPAREN x = IDENT COLON a = ty RPAREN TIMES b = ty_product
    { TySigma (x, a, b) }
  (* Non-dependent product *)
  | a = ty_app TIMES b = ty_product
    { TySigma ("_", a, b) }

ty_app:
  | t = ty_atom { t }
  | f = ty_app a = ty_atom { TyApp (f, a) }

ty_atom:
  | LPAREN t = ty RPAREN { t }
  | x = IDENT { TyVar x }
  | SET { TySet None }
  | SET n = NUM { TySet (Some n) }
  | PROP { TySet (Some 0) }

(* Patterns *)
pattern:
  | p = pattern_app { p }

pattern_app:
  | p = pattern_atom { p }
  | c = IDENT ps = nonempty_list(pattern_atom) { PCon (c, ps) }

pattern_atom:
  | LPAREN p = pattern RPAREN { p }
  | LPAREN a = pattern COMMA b = pattern RPAREN { PPair (a, b) }
  | LPAREN RPAREN { PUnit }
  | x = IDENT { PVar x }
  | UNDERSCORE { PWild }

(* Terms *)
term:
  | t = term_infix { t }
  | LAMBDA bindings = nonempty_list(lambda_binding) ARROW body = term
    { List.fold_right (fun b acc ->
        match b with
        | `Untyped x -> TLam (x, acc)
        | `Typed (x, ty) -> TLamTy (x, ty, acc)
      ) bindings body }
  | LAMBDA bindings = nonempty_list(lambda_binding) DOT body = term
    { List.fold_right (fun b acc ->
        match b with
        | `Untyped x -> TLam (x, acc)
        | `Typed (x, ty) -> TLamTy (x, ty, acc)
      ) bindings body }
  | CASE e = term OF branches = case_branches
    { let (l, r) = branches in TCase (e, l, r) }
  | LET x = IDENT EQ t = term IN body = term
    { TLet (x, None, t, body) }
  | LET x = IDENT COLON ty = ty EQ t = term IN body = term
    { TLet (x, Some ty, t, body) }

lambda_binding:
  | x = IDENT { `Untyped x }
  | LPAREN x = IDENT COLON ty = ty RPAREN { `Typed (x, ty) }
  | LBRACE x = IDENT COLON ty = ty RBRACE { `Typed (x, ty) }
  | LBRACE x = IDENT RBRACE { `Untyped x }

case_branches:
  | INL x = IDENT ARROW l = term BAR INR y = IDENT ARROW r = term
    { ((x, l), (y, r)) }
  | LBRACE INL x = IDENT ARROW l = term SEMI INR y = IDENT ARROW r = term RBRACE
    { ((x, l), (y, r)) }

term_infix:
  | t = term_app { t }

term_app:
  | t = term_atom { t }
  | f = term_app a = term_arg { TApp (f, a) }

term_arg:
  | t = term_atom { t }
  (* Implicit argument *)
  | LBRACE t = term RBRACE { t }

term_atom:
  | LPAREN t = term RPAREN { t }
  | LPAREN a = term COMMA b = term RPAREN { TPair (a, b) }
  | x = IDENT { TVar x }
  | UNDERSCORE { THole }
  | REFL { TRefl }
  | FST { TVar "fst" }
  | SND { TVar "snd" }
  | INL { TVar "inl" }
  | INR { TVar "inr" }
  | LPAREN t = term COLON ty = ty RPAREN { TAnn (t, ty) }

(* Credence annotations for CredTT *)
credence_annotation:
  | (* empty *) { None }
  | LWEIGHT c = credence RWEIGHT { Some c }

credence:
  | c = credence_mul { c }

credence_mul:
  | c = credence_atom { c }
  | a = credence_mul CDOT b = credence_atom { CMul (a, b) }
  | a = credence_mul TIMES b = credence_atom { CMul (a, b) }

credence_atom:
  | LPAREN c = credence RPAREN { c }
  | BBZERO { CZero }
  | BBONE { COne }
  | n = NUM SLASH d = NUM { CRat (n, d) }
  | NUM { if $1 = 0 then CZero else if $1 = 1 then COne else CVar (string_of_int $1) }
  | x = IDENT { CVar x }
  | NEG c = credence_atom { CNeg c }
  | UNDERSCORE { CInfer }  (* _ for inferred credence *)
  (* Dependent credences: c(x) syntax *)
  | x = IDENT LPAREN y = IDENT RPAREN { CDep (y, CVar x) }
  (* Supremum: sup x. c *)
  | SUP x = IDENT DOT c = credence { CSup (x, c) }
  (* Infimum: inf x. c *)
  | WINF x = IDENT DOT c = credence { CInf (x, c) }
