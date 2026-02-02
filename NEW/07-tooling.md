# Tooling: Is Agda the Right Choice?

## The Problem

Agda assumes MLTT. If we're claiming types EMERGE from credences,
using Agda is circular:

```
Agda = MLTT implementation
CredTT in Agda = "Look, types emerge!" (using types to define it)
```

This is like proving set theory's consistency using set theory.

## What Agda Gives Us

**Good:**
- Dependent types for expressing complex relationships
- Type checker verifies our proofs
- Mature ecosystem

**Bad:**
- Types are primitive (we claim they're derived)
- Assumes MLTT (we claim MLTT emerges)
- Can't directly represent "untyped" terms

## Alternatives to Agda

### 1. Raw Implementation (OCaml, Haskell, Rust)

Build the credence system from scratch:
```
type credence = float  (* or symbolic *)
type term = Var of int | Lam of term | App of term * term | ...
type judgment = term * credence  (* Γ ⊢ t @ c *)
```

**Pro:** No type-theoretic assumptions
**Con:** No verification, easy to make mistakes

### 2. Metamath / Lean 4 Foundation

Use a more minimal foundation:
- Metamath: Just substitution, no types at the meta level
- Lean 4: Can disable kernel features

**Pro:** Closer to "types emerge"
**Con:** Harder to work with

### 3. Self-Hosted

Build CredTT, then reimplement CredTT IN CredTT:
```
CredTT₀ (in OCaml) → CredTT₁ (in CredTT₀) → ...
```

**Pro:** True self-foundation
**Con:** Massive undertaking

### 4. Categorical/Algebraic Tools

Use tools designed for category theory:
- Globular (for higher categories)
- Catlab (categorical computation)

**Pro:** Matches "types as credence predicates" view
**Con:** Not designed for proof

### 5. Probabilistic Programming Languages

Use PPLs that already have credence/probability:
- Hakaru, Anglican, Gen, Pyro

**Pro:** Built for probabilistic reasoning
**Con:** Not foundational, focused on inference

## The Honest Path

### Short Term: Accept the Circularity

Use Agda to SKETCH the system, but acknowledge:
```
"We formalize CredTT in Agda to demonstrate coherence.
This is not a claim that CredTT is more foundational than MLTT.
A truly foundational implementation would require
building from scratch without type-theoretic assumptions."
```

### Medium Term: OCaml Implementation

Build a standalone implementation:
```
1. Credence algebra (abstract)
2. Untyped terms
3. Credence judgments (Γ ⊢ t @ c)
4. Type predicates (Term → C)
5. Derived typing (Γ ⊢ t : A @ c)
```

No dependent types at the meta level.

### Long Term: Self-Hosting

If CredTT proves useful, implement it in itself:
```
CredTT written in CredTT
```

This would be genuine self-foundation.

## What Agda SHOULD Be Used For

Agda is appropriate for:
- Exploring the structure (sketch.agda)
- Verifying that instances (Bool, [0,1]) work
- Proving metatheorems ABOUT CredTT

Agda is NOT appropriate for:
- Claiming foundational priority over MLTT
- Asserting "types emerge" (while using types)
- Final implementation of CredTT v2

## Practical Recommendation

```
Phase 1: Agda sketches (current)
         - Explore the ideas
         - Verify coherence
         - Document clearly that this is meta-level

Phase 2: OCaml implementation (next)
         - No type-theoretic meta-language
         - Credence judgments as primitive
         - Types as derived predicates

Phase 3: Self-hosting (future)
         - CredTT type checker in CredTT
         - True foundational status
```

## The Meta-Circular Issue

Every foundation has this problem:

| System | Implemented In | Circularity |
|--------|----------------|-------------|
| ZFC | English + informal reasoning | Can't formalize "informal" |
| MLTT | Agda/Coq (which assume MLTT) | Circular |
| CredTT | Agda (assumes MLTT) | More circular |

The solution is transparency:
- Acknowledge the circularity
- Separate "exploration" from "foundation"
- Plan for self-hosting
