# CredTT Type Checker Sketch

## Overview

A minimal type checker for CredTT in ~1500 lines of OCaml or Haskell.

## Architecture

```
Source Code
    | (parsing)
Raw AST
    | (elaboration)
Core AST with Credences
    | (type checking)
Typed AST / Error
```

## Core Data Types

### Credences

```ocaml
(* Credence algebra: Product De Morgan *)
type credence =
  | CZero                       (* 0 *)
  | COne                        (* 1 *)
  | CMul of credence * credence (* c1 * c2 *)
  | CNeg of credence            (* ~c *)
  | CVar of string              (* credence variable *)

(* Derived: c1 | c2 = ~(~c1 * ~c2) *)
let c_or c1 c2 = CNeg (CMul (CNeg c1, CNeg c2))

(* Simplify credences *)
let rec simplify = function
  | CMul (COne, c) | CMul (c, COne) -> simplify c
  | CMul (CZero, _) | CMul (_, CZero) -> CZero
  | CNeg (CNeg c) -> simplify c
  | CNeg CZero -> COne
  | CNeg COne -> CZero
  | CMul (c1, c2) -> CMul (simplify c1, simplify c2)
  | CNeg c -> CNeg (simplify c)
  | c -> c
```

### Terms and Types

```ocaml
type term =
  (* Variables *)
  | Var of string

  (* Functions *)
  | Lam of string * typ * term        (* lam x:A. b *)
  | App of term * term                (* f a *)

  (* Pairs *)
  | Pair of term * term               (* (a, b) *)
  | Fst of term                       (* pi1 t *)
  | Snd of term                       (* pi2 t *)

  (* Sums *)
  | Inl of term * typ                 (* inl a : A + B *)
  | Inr of term * typ                 (* inr b : A + B *)
  | Case of term * string * term * string * term

  (* Unit and Empty *)
  | Star                              (* star *)
  | Abort of term * typ               (* abort e : A *)

  (* Identity *)
  | Refl of term                      (* refl *)

  (* Universe *)
  | Type of int                       (* Type_i *)

  (* Credence terms *)
  | CTerm of credence                 (* credence as term *)

and typ =
  | TVar of string
  | Pi of string * typ * typ          (* (x : A) -> B *)
  | Sigma of string * typ * typ       (* Sigma(x : A). B *)
  | Sum of typ * typ                  (* A + B *)
  | Empty                             (* 0 *)
  | Unit                              (* 1 *)
  | Id of typ * term * term           (* Id_A(a, b) *)
  | Universe of int                   (* Type_i *)
  | CType                             (* C (credence type) *)
```

### Contexts and Judgments

```ocaml
(* Context entry: variable with type *)
type ctx_entry = string * typ

(* Context *)
type ctx = ctx_entry list

(* Credenced typing judgment: Gamma |- a : A @ c *)
type judgment = {
  ctx : ctx;
  term : term;
  typ : typ;
  credence : credence;
}
```

## Type Checking Algorithm

### Bidirectional Type Checking

```ocaml
(* Infer type and credence of a term *)
let rec infer (ctx : ctx) (t : term) : (typ * credence) result =
  match t with
  | Var x ->
      (* Variables have credence 1 *)
      let* ty = lookup x ctx in
      Ok (ty, COne)

  | App (f, a) ->
      (* Credences multiply *)
      let* (Pi (x, a_ty, b_ty), c_f) = infer ctx f in
      let* c_a = check ctx a a_ty in
      let result_ty = subst x a b_ty in
      Ok (result_ty, CMul (c_f, c_a))

  | Fst t ->
      let* (Sigma (x, a_ty, _), c) = infer ctx t in
      Ok (a_ty, c)

  | Snd t ->
      let* (Sigma (x, a_ty, b_ty), c) = infer ctx t in
      let a = Fst t in
      Ok (subst x a b_ty, c)

  | Star ->
      Ok (Unit, COne)

  | Type i ->
      Ok (Universe (i + 1), COne)

  | CTerm _ ->
      Ok (CType, COne)

  | _ ->
      Error "Cannot infer type; use annotation"

(* Check term against expected type, return credence *)
and check (ctx : ctx) (t : term) (expected : typ) : credence result =
  match t, expected with
  | Lam (x, a_ty, body), Pi (y, a_ty', b_ty) ->
      (* Check domain matches *)
      let* () = check_equal a_ty a_ty' in
      (* Check body in extended context *)
      let ctx' = (x, a_ty) :: ctx in
      let b_ty' = subst y (Var x) b_ty in
      check ctx' body b_ty'

  | Pair (a, b), Sigma (x, a_ty, b_ty) ->
      (* Credences multiply *)
      let* c_a = check ctx a a_ty in
      let b_ty' = subst x a b_ty in
      let* c_b = check ctx b b_ty' in
      Ok (CMul (c_a, c_b))

  | Inl (a, _), Sum (a_ty, _) ->
      check ctx a a_ty

  | Inr (b, _), Sum (_, b_ty) ->
      check ctx b b_ty

  | Refl a, Id (ty, a', b') ->
      (* Check a = a' = b' *)
      let* c = check ctx a ty in
      let* () = check_equal_term a a' in
      let* () = check_equal_term a b' in
      Ok c

  | Abort (e, _), _ ->
      let* c = check ctx e Empty in
      Ok c  (* Any credence works *)

  | _, _ ->
      (* Fall back to inference *)
      let* (inferred, c) = infer ctx t in
      let* () = check_equal inferred expected in
      Ok c
```

### Credence Comparison

```ocaml
(* Check c1 <= c2 (for weakening) *)
let rec credence_leq (c1 : credence) (c2 : credence) : bool =
  match simplify c1, simplify c2 with
  | CZero, _ -> true
  | _, COne -> true
  | c1, c2 -> credence_equal c1 c2

(* Check credence equality *)
and credence_equal (c1 : credence) (c2 : credence) : bool =
  simplify c1 = simplify c2
```

## Evaluation (Optional)

For normalization (needed for type equality):

```ocaml
let rec eval (env : (string * term) list) (t : term) : term =
  match t with
  | Var x ->
      (try List.assoc x env with Not_found -> t)
  | App (f, a) ->
      let f' = eval env f in
      let a' = eval env a in
      (match f' with
       | Lam (x, _, body) -> eval ((x, a') :: env) body
       | _ -> App (f', a'))
  | Lam (x, ty, body) ->
      Lam (x, ty, body)  (* Don't reduce under lambda *)
  | Pair (a, b) ->
      Pair (eval env a, eval env b)
  | Fst t ->
      (match eval env t with
       | Pair (a, _) -> a
       | t' -> Fst t')
  | Snd t ->
      (match eval env t with
       | Pair (_, b) -> b
       | t' -> Snd t')
  | _ -> t
```

## File Structure

```
credtt/
  src/
    credence.ml     -- Credence algebra (~100 lines)
    syntax.ml       -- AST definitions (~100 lines)
    context.ml      -- Context operations (~50 lines)
    eval.ml         -- Evaluation/normalization (~150 lines)
    check.ml        -- Type checking (~400 lines)
    parser.mly      -- Parser (~200 lines)
    lexer.mll       -- Lexer (~100 lines)
    main.ml         -- CLI (~50 lines)
  test/
    examples/       -- Example CredTT programs
  dune             -- Build configuration
```

## Example Program

```
-- CredTT source file

-- Credence-annotated function
def uncertain_id : (A : Type) -> A -> A @ 0.9
  = lam A. lam x. x

-- Pair with joint credence
def pair_example : (A : Type) -> (a : A @ 0.8) -> (b : A @ 0.7) -> A x A @ 0.56
  = lam A. lam a. lam b. (a, b)

-- Classical case: credence 1
def id : (A : Type) -> A -> A @ 1
  = lam A. lam x. x
```

## Implementation Steps

1. **Credence algebra** (1 day)
   - Define credence type
   - Simplification
   - Comparison

2. **Syntax** (1 day)
   - Term and type AST
   - Pretty printing

3. **Type checker** (3 days)
   - Bidirectional algorithm
   - Credence multiplication
   - Context handling

4. **Parser** (2 days)
   - Lexer
   - Parser
   - Concrete syntax

5. **CLI and tests** (1 day)
   - Main entry point
   - Example programs

## Dependencies

OCaml:
- `menhir` (parser generator)
- `dune` (build system)

Haskell alternative:
- `parsec` or `megaparsec`
- `mtl` for monad transformers

## Extensions

1. **Credence inference**: Infer credences from term structure
2. **Universe polymorphism**: Proper universe handling
3. **Holes**: `?` for incomplete terms
4. **REPL**: Interactive mode
5. **Error messages**: Better diagnostics
