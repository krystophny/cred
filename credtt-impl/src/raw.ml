(* Raw AST for Agda-compatible surface syntax *)

type name = string

type implicit = Explicit | Implicit

type pattern =
  | PVar of name
  | PWild
  | PCon of name * pattern list
  | PPair of pattern * pattern
  | PUnit

(* Credence annotation (CredTT extension) *)
type credence =
  | CZero
  | COne
  | CMul of credence * credence
  | CNeg of credence
  | CVar of name
  | CRat of int * int  (* numerator, denominator for rational credences like 1/2 *)
  | CInfer            (* inference variable, credence to be inferred *)
  | CDep of name * credence  (* dependent credence: c(x) where x is bound variable *)
  | CSup of name * credence  (* supremum: sup x. c(x) *)
  | CInf of name * credence  (* infimum: inf x. c(x) *)

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
  | DSig of name * ty * credence option
  | DDef of name * pattern list * term
  | DData of name * telescope * (name * ty) list
  | DRecord of name * telescope * (name * ty) list
  | DOpen of name * name list option
  | DModule of name * decl list
  | DImport of string list * name list option
  | DInfix of assoc * int * name
  | DComment of string
  (* Proof declarations *)
  | DPostulate of name * name * credence         (* name, prop, credence *)
  | DDerive of name * name * credence * name * name  (* name, prop, credence, from, by *)
  | DContradict of name * name                 (* two contradictory props *)
  | DConclude of name * name                   (* conclusion, from *)
  (* Meta-theory declarations for Goedel/consistency *)
  | DProvable of name * name * credence          (* Prov_c(phi): name, prop, credence *)
  | DFixpoint of name * credence                 (* fixpoint name = credence_expr *)
  | DEncode of name * name                       (* encode name = prop (Goedel encoding) *)
  (* Stability assertions *)
  | DStable of name                              (* stable name: assert Stable1 credence *)
  | DUnstable of name                            (* unstable name: assert Unstable0 credence *)

and assoc = ALeft | ARight | ANone

type program = decl list
