# Layer 1: Credence Judgments (No Types)

## The Radical Move

Standard type theory has judgments like:
```
Γ ⊢ t : A           -- "t has type A in context Γ"
```

CredTT v1 extends this to:
```
Γ ⊢ t : A @ c       -- "t has type A at credence c"
```

**But v1 still assumes types exist as primitive syntax.**

CredTT v2 goes further:
```
Γ ⊢ t @ c           -- "t has credence c in context Γ"
```

**No types in the primitive judgment. Only terms and credences.**

## Primitive Syntax

### Terms (Untyped)
```
t, u ::= x                       -- variable
       | λx. t                   -- abstraction
       | t u                     -- application
       | (t, u)                  -- pair
       | fst t | snd t           -- projections
       | inl t | inr t           -- injections
       | case t of inl x → u | inr y → v
       | refl                    -- reflexivity
       | J t u v                 -- J eliminator
```

These are **untyped** lambda terms with pairs, sums, and identity.
There is no type annotation.

### Contexts
```
Γ ::= ·                          -- empty context
    | Γ, x @ c                   -- extend with variable at credence
```

**Note**: Variables have credences, not types!

## The Primitive Judgment

```
Γ ⊢ t @ c
```

Read: "In context Γ, term t has credence c."

### What Does This Mean?

The credence c represents:
- How "certain" we are that t is meaningful/defined
- The "degree of existence" of t
- The probability that t computes to a value

This is deliberately vague at this layer. The interpretation
comes from how credences propagate through term structure.

## Credence Propagation Rules

### Variables
```
(x @ c) ∈ Γ
──────────────── VAR
Γ ⊢ x @ c
```

A variable has the credence assigned in the context.

### Abstraction
```
Γ, x @ c₁ ⊢ t @ c₂
──────────────────────── ABS
Γ ⊢ (λx. t) @ (c₁ ⇒ c₂)
```

A function has credence "if input has c₁, output has c₂."
Using c₁ ⇒ c₂ = ~c₁ + c₂.

**Alternative (multiplicative):**
```
Γ, x @ 1 ⊢ t @ c
──────────────────── ABS-MULT
Γ ⊢ (λx. t) @ c
```

Functions inherit the credence of their body (assuming input is certain).

### Application (The Key Rule)
```
Γ ⊢ f @ c₁    Γ ⊢ a @ c₂
────────────────────────── APP
Γ ⊢ (f a) @ (c₁ * c₂)
```

**Credences multiply in application.**

This is the fundamental rule. It says:
- If f is c₁-certain and a is c₂-certain
- Then (f a) is (c₁ * c₂)-certain

This captures "uncertainty propagates."

### Pairs
```
Γ ⊢ t @ c₁    Γ ⊢ u @ c₂
────────────────────────── PAIR
Γ ⊢ (t, u) @ (c₁ * c₂)
```

A pair is as certain as both components (conjunction).

### Projections
```
Γ ⊢ p @ c
────────────── FST
Γ ⊢ fst p @ c

Γ ⊢ p @ c
────────────── SND
Γ ⊢ snd p @ c
```

Projections preserve credence.

### Injections
```
Γ ⊢ t @ c
────────────────── INL
Γ ⊢ inl t @ c

Γ ⊢ t @ c
────────────────── INR
Γ ⊢ inr t @ c
```

Injections preserve credence.

### Case Analysis
```
Γ ⊢ e @ c₀    Γ, x @ c₀ ⊢ u @ c₁    Γ, y @ c₀ ⊢ v @ c₂
───────────────────────────────────────────────────────── CASE
Γ ⊢ case e of inl x → u | inr y → v @ (c₀ * (c₁ + c₂))
```

**Or simpler (assuming branches have same credence):**
```
Γ ⊢ e @ c₀    Γ, x @ c₀ ⊢ u @ c    Γ, y @ c₀ ⊢ v @ c
─────────────────────────────────────────────────────── CASE-SIMPLE
Γ ⊢ case e of inl x → u | inr y → v @ (c₀ * c)
```

### Identity
```
────────────────── REFL
Γ ⊢ refl @ 1
```

Reflexivity has credence 1 (certain).

### J Eliminator
```
Γ ⊢ p @ c₁    Γ ⊢ d @ c₂    Γ ⊢ a @ c₃
──────────────────────────────────────── J
Γ ⊢ J p d a @ (c₁ * c₂ * c₃)
```

## What We Have Now

At this layer:
- Untyped terms with standard constructs
- Contexts assigning credences to variables
- A judgment Γ ⊢ t @ c with propagation rules

What we DON'T have:
- Types
- Typing judgments
- Type formation rules

**Terms exist independently of types.**
Types will emerge as patterns in credence behavior.

## The Crucial Observation

Consider two terms t and u. We can ask:
- Do they have the same credence in all contexts?
- Do they "behave the same" with respect to credence?

If Γ ⊢ t @ c ⟺ Γ ⊢ u @ c for all Γ and c, then t and u are
**credence-equivalent**.

This equivalence will give rise to types in the next layer.
