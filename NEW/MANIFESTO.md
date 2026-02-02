# CredTT v2: Types Emerge from Credence

## The Problem with CredTT v1

CredTT v1 claims "types emerge from credence structure" but actually does the opposite:

```
v1 CLAIMS:     Credence algebra → Type formers → MLTT
v1 ACTUALLY:   Type syntax (given) + Credence annotations (bolted on)
```

The types in v1 are **primitive syntax**, defined independently of credences.
Credences are **decorations** on judgments, not the foundation.

## The New Vision: Credence First, Types Derived

```
v2 ARCHITECTURE:

Layer 0: Credence Algebra
         (C, 1, 0, *, ~, ≤) — De Morgan algebra

Layer 1: Credence Judgments
         Γ ⊢ t @ c — "t has credence c in context Γ"
         No types yet! Just terms and credences.

Layer 2: Type Emergence
         Types := equivalence classes of credence-coherent terms
         A ≃ B iff ∀t,c: (Γ ⊢ t : A @ c) ⟺ (Γ ⊢ t : B @ c)

Layer 3: Type Formers (Derived)
         Π, Σ, +, Id arise from credence operations
         Not given as syntax — constructed from Layer 0-2

Layer 4: MLTT (Boolean Collapse)
         When C = {0,1}, recover standard type theory
```

## Core Principles

### 1. No Primitive Type Syntax

In v1:
```agda
data Ty : Set where
  _⇒_ : Ty → Ty → Ty   -- Given as syntax
```

In v2:
```
Types are not syntax. Types are DERIVED STRUCTURE.
A "type" is an equivalence class of terms under credence-coherence.
```

### 2. Judgments Are Primary

The only primitive judgment form:
```
Γ ⊢ t @ c
```
Read: "In context Γ, term t has credence c."

There is NO judgment `Γ ⊢ t : A @ c` at the primitive level.
The `: A` part is DERIVED from credence structure.

### 3. Types Are Credence Predicates

A "type" is a function:
```
A : Term → C
```
assigning to each term its "credence of membership."

Two types are equal when they assign the same credences:
```
A = B  iff  ∀t: A(t) = B(t)
```

### 4. Type Formers Are Credence Operations

```
(Π A B)(f) := inf_{t} [ A(t) ⇒ B(f t) ]
(Σ A B)(p) := A(fst p) * B(snd p)
(A + B)(e) := case e of inl a → A(a) | inr b → B(b)
```

The type formers are DEFINED in terms of credence algebra operations,
not given as primitive syntax.

### 5. MLTT Is the Boolean Collapse

When C = Bool:
- Credence predicates become characteristic functions
- Types become sets (subsets of terms)
- Type formers become standard constructions
- We recover MLTT (without Unit/Empty — those are credence 1/0)

## What This Achieves

1. **Genuine emergence**: Types are constructed, not assumed
2. **Credences truly primitive**: Everything derives from (C, *, ~, ≤)
3. **No Unit/Empty needed**: 1 and 0 are credences, not types
4. **Philosophical coherence**: The claim matches the formalization

## Document Structure

- `01-credence-algebra.md` — The primitive layer
- `02-judgments.md` — Credence judgments without types
- `03-types-emerge.md` — How types arise as equivalence classes
- `04-type-formers.md` — Deriving Π, Σ, +, Id from credence ops
- `05-mltt-collapse.md` — The Boolean case gives MLTT
- `sketch.agda` — Formal sketch in Agda
