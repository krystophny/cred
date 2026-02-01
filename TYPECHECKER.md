# ProbTT Type Checker Sketch

## Overview

A minimal type checker for ProbTT in ~1500 lines of OCaml or Haskell.

## Architecture

```
Source Code
    ↓ (parsing)
Raw AST
    ↓ (elaboration)
Core AST with Weights
    ↓ (type checking)
Typed AST / Error
```

## Core Data Types

### Weights

```ocaml
(* Weight algebra: Product De Morgan *)
type weight =
  | WZero                    (* 0 *)
  | WOne                     (* 1 *)
  | WMul of weight * weight  (* w · v *)
  | WNeg of weight           (* ¬w *)
  | WVar of string           (* weight variable *)

(* Derived: w ∨ v = ¬(¬w · ¬v) *)
let w_or w v = WNeg (WMul (WNeg w, WNeg v))

(* Simplify weights *)
let rec simplify = function
  | WMul (WOne, w) | WMul (w, WOne) -> simplify w
  | WMul (WZero, _) | WMul (_, WZero) -> WZero
  | WNeg (WNeg w) -> simplify w
  | WNeg WZero -> WOne
  | WNeg WOne -> WZero
  | WMul (w, v) -> WMul (simplify w, simplify v)
  | WNeg w -> WNeg (simplify w)
  | w -> w
```

### Terms and Types

```ocaml
type term =
  (* Variables *)
  | Var of string

  (* Functions *)
  | Lam of string * typ * term        (* λx:A. b *)
  | App of term * term                (* f a *)

  (* Pairs *)
  | Pair of term * term               (* (a, b) *)
  | Fst of term                       (* π₁ t *)
  | Snd of term                       (* π₂ t *)

  (* Sums *)
  | Inl of term * typ                 (* inl a : A + B *)
  | Inr of term * typ                 (* inr b : A + B *)
  | Case of term * string * term * string * term

  (* Unit and Empty *)
  | Star                              (* ★ *)
  | Abort of term * typ               (* abort e : A *)

  (* Identity *)
  | Refl of term                      (* refl *)

  (* Universe *)
  | Type of int                       (* Type_i *)

  (* Weight terms *)
  | WTerm of weight                   (* weight as term *)

and typ =
  | TVar of string
  | Pi of string * typ * typ          (* (x : A) → B *)
  | Sigma of string * typ * typ       (* Σ(x : A). B *)
  | Sum of typ * typ                  (* A + B *)
  | Empty                             (* 𝟎 *)
  | Unit                              (* 𝟏 *)
  | Id of typ * term * term           (* Id_A(a, b) *)
  | Universe of int                   (* Type_i *)
  | WType                             (* W (weight type) *)
```

### Contexts and Judgments

```ocaml
(* Context entry: variable with type *)
type ctx_entry = string * typ

(* Context *)
type ctx = ctx_entry list

(* Weighted typing judgment: Γ ⊢ a : A @ w *)
type judgment = {
  ctx : ctx;
  term : term;
  typ : typ;
  weight : weight;
}
```

## Type Checking Algorithm

### Bidirectional Type Checking

```ocaml
(* Infer type and weight of a term *)
let rec infer (ctx : ctx) (t : term) : (typ * weight) result =
  match t with
  | Var x ->
      (* Variables have weight 1 *)
      let* ty = lookup x ctx in
      Ok (ty, WOne)

  | App (f, a) ->
      (* Weights multiply *)
      let* (Pi (x, a_ty, b_ty), w_f) = infer ctx f in
      let* w_a = check ctx a a_ty in
      let result_ty = subst x a b_ty in
      Ok (result_ty, WMul (w_f, w_a))

  | Fst t ->
      let* (Sigma (x, a_ty, _), w) = infer ctx t in
      Ok (a_ty, w)

  | Snd t ->
      let* (Sigma (x, a_ty, b_ty), w) = infer ctx t in
      let a = Fst t in
      Ok (subst x a b_ty, w)

  | Star ->
      Ok (Unit, WOne)

  | Type i ->
      Ok (Universe (i + 1), WOne)

  | WTerm _ ->
      Ok (WType, WOne)

  | _ ->
      Error "Cannot infer type; use annotation"

(* Check term against expected type, return weight *)
and check (ctx : ctx) (t : term) (expected : typ) : weight result =
  match t, expected with
  | Lam (x, a_ty, body), Pi (y, a_ty', b_ty) ->
      (* Check domain matches *)
      let* () = check_equal a_ty a_ty' in
      (* Check body in extended context *)
      let ctx' = (x, a_ty) :: ctx in
      let b_ty' = subst y (Var x) b_ty in
      check ctx' body b_ty'

  | Pair (a, b), Sigma (x, a_ty, b_ty) ->
      (* Weights multiply *)
      let* w_a = check ctx a a_ty in
      let b_ty' = subst x a b_ty in
      let* w_b = check ctx b b_ty' in
      Ok (WMul (w_a, w_b))

  | Inl (a, _), Sum (a_ty, _) ->
      check ctx a a_ty

  | Inr (b, _), Sum (_, b_ty) ->
      check ctx b b_ty

  | Refl a, Id (ty, a', b') ->
      (* Check a = a' = b' *)
      let* w = check ctx a ty in
      let* () = check_equal_term a a' in
      let* () = check_equal_term a b' in
      Ok w

  | Abort (e, _), _ ->
      let* w = check ctx e Empty in
      Ok w  (* Any weight works *)

  | _, _ ->
      (* Fall back to inference *)
      let* (inferred, w) = infer ctx t in
      let* () = check_equal inferred expected in
      Ok w
```

### Weight Comparison

```ocaml
(* Check w₁ ≤ w₂ (for weakening) *)
let rec weight_leq (w1 : weight) (w2 : weight) : bool =
  match simplify w1, simplify w2 with
  | WZero, _ -> true
  | _, WOne -> true
  | w1, w2 -> weight_equal w1 w2

(* Check weight equality *)
and weight_equal (w1 : weight) (w2 : weight) : bool =
  simplify w1 = simplify w2
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
probtt/
  src/
    weight.ml       -- Weight algebra (~100 lines)
    syntax.ml       -- AST definitions (~100 lines)
    context.ml      -- Context operations (~50 lines)
    eval.ml         -- Evaluation/normalization (~150 lines)
    check.ml        -- Type checking (~400 lines)
    parser.mly      -- Parser (~200 lines)
    lexer.mll       -- Lexer (~100 lines)
    main.ml         -- CLI (~50 lines)
  test/
    examples/       -- Example ProbTT programs
  dune             -- Build configuration
```

## Example Program

```
-- ProbTT source file

-- Weight-annotated function
def uncertain_id : (A : Type) -> A -> A @ 0.9
  = λA. λx. x

-- Pair with joint weight
def pair_example : (A : Type) -> (a : A @ 0.8) -> (b : A @ 0.7) -> A × A @ 0.56
  = λA. λa. λb. (a, b)

-- Classical case: weight 1
def id : (A : Type) -> A -> A @ 1
  = λA. λx. x
```

## Implementation Steps

1. **Weight algebra** (1 day)
   - Define weight type
   - Simplification
   - Comparison

2. **Syntax** (1 day)
   - Term and type AST
   - Pretty printing

3. **Type checker** (3 days)
   - Bidirectional algorithm
   - Weight multiplication
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

1. **Weight inference**: Infer weights from term structure
2. **Universe polymorphism**: Proper universe handling
3. **Holes**: `?` for incomplete terms
4. **REPL**: Interactive mode
5. **Error messages**: Better diagnostics
