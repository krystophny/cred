# Layer 2: Types Emerge

## The Key Idea

We have terms and credence judgments. Now we derive types.

**A type is not primitive syntax. A type is a credence predicate.**

## Definition: Credence Predicate

A **credence predicate** is a function:
```
P : Term → C
```

It assigns to each term t a credence P(t) ∈ C.

Intuition: P(t) is "the credence that t belongs to / satisfies P."

## Definition: Type

A **type** is a credence predicate that is:
1. **Closed under credence operations** (coherent)
2. **Respects term equivalence** (well-defined)

Formally, a type A : Term → C satisfies:
```
1. A(t) * A(u) ≤ A((t, u))           -- pairs
2. A((t, u)) ≤ A(t) and A((t,u)) ≤ A(u)  -- projections
3. A(f) * A(a) ≤ A(f a)             -- application
4. (more conditions for other constructors)
```

## Definition: Typing Judgment (Derived)

We can now DEFINE the typing judgment:
```
Γ ⊢ t : A @ c   :=   Γ ⊢ t @ c  AND  A(t) ≥ c
```

Read: "t has type A at credence c" means:
- t has credence c in context Γ
- A assigns to t a credence at least c

**This is a DEFINITION, not a primitive.**

## Definition: Type Equality

Two types A and B are equal when:
```
A = B   iff   ∀t: A(t) = B(t)
```

Types are equal when they assign the same credences to all terms.

## Example: The "Everything" Type (Universe Analog)

Define:
```
𝒰(t) := 1    for all t
```

Every term has credence 1 in 𝒰. This is the "top type" or universe.

## Example: The "Nothing" Type (Empty Analog)

Define:
```
∅(t) := 0    for all t
```

Every term has credence 0 in ∅. This is the "bottom type."

**Note**: ∅ is NOT a type we add. It's a credence predicate that
naturally exists: the constant-0 function.

## Example: A Singleton Type

For a specific term a, define:
```
{a}(t) := if t ≡ a then 1 else 0
```

This is the type containing only a (at credence 1).

## Example: Function Types (Preview)

Given types A and B, define:
```
(A → B)(f) := inf_{t} [ A(t) ⇒ B(f t) ]
            = inf_{t} [ ~A(t) + B(f t) ]
```

Read: f has type A → B to the degree that:
"for all t, if t : A then f t : B"

The infimum ensures this holds for ALL inputs.

## The Emergence Theorem (Sketch)

**Theorem**: The collection of types (credence predicates satisfying
coherence conditions) forms a category with:
- Objects: Types (credence predicates)
- Morphisms: Functions respecting credence structure

**Theorem**: This category has products, coproducts, and exponentials
(under suitable conditions on C).

**Theorem**: When C = {0, 1}, this category is equivalent to Set
(or the category of types in MLTT).

## Why This Is "Emergence"

In standard type theory:
```
Types are GIVEN as syntax
Terms are TYPED by the given types
```

In CredTT v2:
```
Credences are GIVEN (Layer 0)
Terms exist with credence judgments (Layer 1)
Types EMERGE as credence predicates (Layer 2)
```

Types are not assumed. They are constructed from credence structure.

## The Typing Relation Revisited

We now have THREE ways to understand "t has type A":

### Level 1: Judgment (Primitive)
```
Γ ⊢ t @ c     -- t has credence c
```

### Level 2: Predicate (Derived)
```
A(t) = c      -- A assigns credence c to t
```

### Level 3: Typing (Defined)
```
Γ ⊢ t : A @ c := (Γ ⊢ t @ c) ∧ (A(t) ≥ c)
```

The typing judgment combines the primitive credence judgment
with the derived type predicate.

## Subtyping from Credence Ordering

A natural subtyping relation emerges:
```
A ≤ B   iff   ∀t: A(t) ≤ B(t)
```

If A(t) ≤ B(t) for all t, then anything in A is also in B
(with at least as much credence).

This gives:
```
∅ ≤ A ≤ 𝒰     for all types A
```

The empty type is least, the universe is greatest.

## Connection to Realizability

This construction is reminiscent of **realizability**:
- In realizability, types are sets of "realizers" (computational evidence)
- Here, types are "credence assignments" (graded evidence)

The difference:
- Realizability: t ∈ A is binary (yes/no)
- CredTT v2: A(t) ∈ C is graded (how much)

CredTT v2 is **graded realizability**.

## What Comes Next

We have:
- Types as credence predicates
- A derived typing judgment
- Subtyping from credence ordering

Next, we show that the standard type formers (Π, Σ, +, Id)
are DERIVABLE from credence operations.
