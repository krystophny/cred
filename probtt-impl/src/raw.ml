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
  | WRat of int * int  (* numerator, denominator for rational weights like 1/2 *)

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
  (* Proof declarations *)
  | DPostulate of name * name * weight         (* name, prop, weight *)
  | DDerive of name * name * weight * name * name  (* name, prop, weight, from, by *)
  | DContradict of name * name                 (* two contradictory props *)
  | DConclude of name * name                   (* conclusion, from *)
  (* Meta-theory declarations for Gödel/consistency *)
  | DProvable of name * name * weight          (* Prov_w(φ): name, prop, weight *)
  | DFixpoint of name * weight                 (* fixpoint name = weight_expr *)
  | DEncode of name * name                     (* encode name = prop (Gödel encoding) *)

and assoc = ALeft | ARight | ANone

type program = decl list
