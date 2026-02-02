(* AST for CredTT using de Bruijn indices

   No Empty type: impossibility is credence 0, not a special type.
   No Unit type: certainty is credence 1, not a special type.

   Types: Base, Pi, Sigma, +, Id

   LIMITATION (Issue #110): No source location tracking
   The AST types do not include source location information. This means:
   - Error messages show "v0" instead of user-provided variable names
   - Cannot point to specific source locations in errors
   - IDE integration is limited without location info

   Future work: Add location tracking by wrapping AST nodes with
   { value: 'a; loc: loc } where loc = { file; line; col }. *)

type ty =
  | TBase of int
  | TPi of ty * ty
  | TSigma of ty * ty
  | TSum of ty * ty
  | TId of ty * term * term

and term =
  | Var of int
  | Lam of ty * term
  | App of term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | Inl of term
  | Inr of term
  | Case of term * term * term
  | Refl
  | J of ty * term * term

let rec pp_ty fmt = function
  | TBase i -> Format.fprintf fmt "Base%d" i
  | TPi (a, b) ->
      Format.fprintf fmt "(%a -> %a)" pp_ty a pp_ty b
  | TSigma (a, b) ->
      Format.fprintf fmt "(%a * %a)" pp_ty a pp_ty b
  | TSum (a, b) ->
      Format.fprintf fmt "(%a + %a)" pp_ty a pp_ty b
  | TId (a, t1, t2) ->
      Format.fprintf fmt "Id(%a, %a, %a)" pp_ty a pp_term t1 pp_term t2

and pp_term fmt = function
  | Var i -> Format.fprintf fmt "v%d" i
  | Lam (ty, body) ->
      Format.fprintf fmt "(lam : %a. %a)" pp_ty ty pp_term body
  | App (f, a) ->
      Format.fprintf fmt "(%a %a)" pp_term f pp_term a
  | Pair (a, b) ->
      Format.fprintf fmt "(%a, %a)" pp_term a pp_term b
  | Fst t -> Format.fprintf fmt "(fst %a)" pp_term t
  | Snd t -> Format.fprintf fmt "(snd %a)" pp_term t
  | Inl t -> Format.fprintf fmt "(inl %a)" pp_term t
  | Inr t -> Format.fprintf fmt "(inr %a)" pp_term t
  | Case (e, l, r) ->
      Format.fprintf fmt "(case %a of %a | %a)" pp_term e pp_term l pp_term r
  | Refl -> Format.fprintf fmt "refl"
  | J (m, d, p) ->
      Format.fprintf fmt "(J %a %a %a)" pp_ty m pp_term d pp_term p

let ty_to_string ty =
  let buf = Buffer.create 64 in
  let fmt = Format.formatter_of_buffer buf in
  pp_ty fmt ty;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let term_to_string t =
  let buf = Buffer.create 64 in
  let fmt = Format.formatter_of_buffer buf in
  pp_term fmt t;
  Format.pp_print_flush fmt ();
  Buffer.contents buf
