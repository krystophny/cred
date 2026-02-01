(* Raw AST for Agda-compatible surface syntax *)

type name = string

type implicit = Explicit | Implicit

type pattern =
  | PVar of name
  | PWild
  | PCon of name * pattern list
  | PPair of pattern * pattern
  | PUnit

(* Weight annotation (ProbTT extension) *)
type weight =
  | WZero
  | WOne
  | WMul of weight * weight
  | WNeg of weight
  | WVar of name

type term =
  | TVar of name
  | TApp of term * term
  | TLam of name * term
  | TLamTy of name * ty * term
  | TPair of term * term
  | TFst of term
  | TSnd of term
  | TInl of term
  | TInr of term
  | TCase of term * (name * term) * (name * term)
  | TUnit
  | TAbort of ty * term
  | TRefl
  | TJ of ty * term * term
  | TAnn of term * ty
  | THole
  | TLet of name * ty option * term * term
  | TWhere of term * decl list

and ty =
  | TyVar of name
  | TyApp of ty * ty
  | TyArrow of ty * ty
  | TyPi of name * implicit * ty * ty
  | TySigma of name * ty * ty
  | TySum of ty * ty
  | TyUnit
  | TyEmpty
  | TyId of ty * term * term
  | TySet of int option

and telescope = (name * implicit * ty) list

and decl =
  | DSig of name * ty * weight option
  | DDef of name * pattern list * term
  | DData of name * telescope * (name * ty) list
  | DRecord of name * telescope * (name * ty) list
  | DOpen of name * name list option
  | DModule of name * decl list
  | DImport of string list * name list option
  | DInfix of assoc * int * name
  | DComment of string

and assoc = ALeft | ARight | ANone

type program = decl list
