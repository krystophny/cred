# Layer 3: Deriving Type Formers

## The Goal

Show that Π, Σ, +, and Id types are not primitive syntax but
**derived constructions** from credence operations.

Each type former corresponds to a credence algebra operation:
```
Π  ↔  inf and ⇒ (implication)
Σ  ↔  * (multiplication/conjunction)
+  ↔  + (disjunction)
Id ↔  equality in C
```

## Product Types (Σ)

### Definition

Given types A : Term → C and B : Term → Term → C (dependent),
define the sigma type:
```
(Σ x:A. B x)(p) := A(fst p) * B(fst p)(snd p)
```

For non-dependent pairs:
```
(A × B)(p) := A(fst p) * B(snd p)
```

### Intuition

A pair (a, b) has credence in Σ A B equal to:
- The credence that a : A, TIMES
- The credence that b : B(a)

This is conjunction: both components must hold.

### The Rules Emerge

**Introduction**:
```
Γ ⊢ a : A @ c₁    Γ ⊢ b : B(a) @ c₂
────────────────────────────────────
Γ ⊢ (a, b) : Σ x:A. B x @ c₁ * c₂
```

This FOLLOWS from the definition:
```
(Σ x:A. B x)((a,b)) = A(a) * B(a)(b) ≥ c₁ * c₂
```

**Elimination**:
```
Γ ⊢ p : Σ x:A. B x @ c
───────────────────────
Γ ⊢ fst p : A @ c

Γ ⊢ p : Σ x:A. B x @ c
───────────────────────
Γ ⊢ snd p : B(fst p) @ c
```

This follows because:
```
(Σ x:A. B x)(p) = A(fst p) * B(fst p)(snd p) ≤ A(fst p)
```

## Function Types (Π)

### Definition

Given types A : Term → C and B : Term → Term → C,
define the pi type:
```
(Π x:A. B x)(f) := inf_{t : Term} [ A(t) ⇒ B(t)(f t) ]
                 = inf_{t : Term} [ ~A(t) + B(t)(f t) ]
```

For non-dependent functions:
```
(A → B)(f) := inf_{t} [ A(t) ⇒ B(f t) ]
```

### Intuition

f has credence in Π A B equal to:
- The infimum over all possible inputs t of:
- "If t : A then f t : B(t)"

This is universal quantification with implication.

### Why Infimum?

The infimum ensures f works for ALL inputs:
```
(Π A B)(f) ≤ A(t) ⇒ B(t)(f t)   for each t
```

If there's even one bad input, the credence drops.

### The Rules Emerge

**Introduction**:
```
Γ, x : A @ 1 ⊢ t : B(x) @ c
────────────────────────────
Γ ⊢ λx.t : Π x:A. B x @ c
```

This holds because:
```
(Π x:A. B x)(λx.t) = inf_{a} [A(a) ⇒ B(a)((λx.t) a)]
                    = inf_{a} [A(a) ⇒ B(a)(t[a/x])]
                    ≥ c   (by the premise)
```

**Elimination** (Application):
```
Γ ⊢ f : Π x:A. B x @ c₁    Γ ⊢ a : A @ c₂
──────────────────────────────────────────
Γ ⊢ f a : B(a) @ c₁ * c₂
```

This follows from:
```
(Π x:A. B x)(f) ≤ A(a) ⇒ B(a)(f a)
```
Combined with A(a) ≥ c₂, we get B(a)(f a) ≥ c₁ * c₂.

Actually, the multiplication comes from our primitive APP rule,
combined with the type predicate constraints.

## Sum Types (+)

### Definition

Given types A : Term → C and B : Term → C,
define the sum type:
```
(A + B)(e) := case e of
               | inl a → A(a)
               | inr b → B(b)
               | _     → 0
```

Or using credence disjunction:
```
(A + B)(e) := A(extract_left e) + B(extract_right e)
```

where only one of extract_left/extract_right is defined.

### Simpler Formulation

```
(A + B)(inl a) := A(a)
(A + B)(inr b) := B(b)
(A + B)(other) := 0
```

### The Rules Emerge

**Left Introduction**:
```
Γ ⊢ a : A @ c
──────────────────────
Γ ⊢ inl a : A + B @ c
```

Follows from: (A + B)(inl a) = A(a) ≥ c.

**Right Introduction**:
```
Γ ⊢ b : B @ c
──────────────────────
Γ ⊢ inr b : A + B @ c
```

Follows from: (A + B)(inr b) = B(b) ≥ c.

**Elimination**:
```
Γ ⊢ e : A + B @ c₀
Γ, x : A @ c₀ ⊢ u : C @ c
Γ, y : B @ c₀ ⊢ v : C @ c
────────────────────────────────────────────
Γ ⊢ case e of inl x → u | inr y → v : C @ c₀ * c
```

## Identity Types (Id)

### Definition

Given a type A and terms a, b, define:
```
(Id_A a b)(p) := [a ≡ b] * A(a) * A(b)
```

where [a ≡ b] is:
- 1 if a and b are definitionally equal
- 0 otherwise (or some intermediate credence for "approximate" equality)

### Simpler (Exact Equality)

```
(Id_A a b)(refl) := if a ≡ b then A(a) else 0
(Id_A a b)(other) := 0
```

### For Graded Equality

We could define a graded notion:
```
(Id_A a b)(p) := similarity(a, b) * A(a)
```

where similarity : Term × Term → C measures "how equal" a and b are.

### The Rules Emerge

**Introduction** (Reflexivity):
```
Γ ⊢ a : A @ c
──────────────────────
Γ ⊢ refl : Id_A a a @ c
```

Follows from: (Id_A a a)(refl) = A(a) ≥ c.

**Elimination** (J):
```
Γ ⊢ p : Id_A a b @ c₁
Γ ⊢ d : C(a, a, refl) @ c₂
Γ ⊢ a : A @ c₃
────────────────────────────
Γ ⊢ J(p, d, a) : C(a, b, p) @ c₁ * c₂ * c₃
```

The J eliminator says: if we can prove C for the reflexivity case,
we can prove it for any equality proof.

## Summary: Type Formers as Credence Operations

| Type Former | Credence Operation | Formula |
|-------------|-------------------|---------|
| Σ x:A. B | Multiplication (*) | A(fst p) * B(fst p)(snd p) |
| Π x:A. B | Inf + Implication | inf_t [A(t) ⇒ B(t)(f t)] |
| A + B | Disjunction | A(a) if inl, B(b) if inr |
| Id_A a b | Equality test | [a ≡ b] * A(a) |

## The Remarkable Fact

The type formers of dependent type theory are not arbitrary.
They correspond exactly to the operations of the credence algebra:

```
* (conjunction)  →  Σ (dependent pairs)
⇒ (implication)  →  Π (dependent functions)
+ (disjunction)  →  + (sums/coproducts)
= (equality)     →  Id (identity types)
```

This is why types "emerge" from credences:
**Type formers ARE credence operations on predicates.**

## What About Unit and Empty?

In this framework:
```
Unit := λt. 1      -- constant 1 predicate (always true)
Empty := λt. 0     -- constant 0 predicate (always false)
```

These are not special types to add. They are the trivial predicates
that exist in any credence algebra.

But notice:
- Unit is the "top" type (everything has credence 1)
- Empty is the "bottom" type (everything has credence 0)

The type structure has natural bounds from the credence algebra.
