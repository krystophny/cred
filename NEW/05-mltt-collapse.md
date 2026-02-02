# Layer 4: MLTT as Boolean Collapse

## The Collapse Theorem

When the credence algebra is Boolean ({0, 1} with AND, NOT):
```
C = {0, 1}
* = AND
~ = NOT
+ = OR
≤ = standard
```

The entire CredTT v2 system collapses to standard MLTT.

## Why Collapse Happens

### Credence Predicates Become Characteristic Functions

A credence predicate A : Term → {0,1} is exactly a **set** of terms:
```
A = { t | A(t) = 1 }
```

The predicate either accepts (1) or rejects (0) each term.

### Types Become Sets

Types (as credence predicates) become sets of terms.
Two types are equal iff they contain the same terms.

### Subtyping Becomes Subset

```
A ≤ B   iff   ∀t: A(t) ≤ B(t)
        iff   ∀t: A(t) = 1 → B(t) = 1
        iff   A ⊆ B
```

Subtyping is just subset inclusion.

## Type Formers Collapse

### Π Collapses to Standard Function Type

```
(Π x:A. B x)(f) = inf_t [A(t) ⇒ B(t)(f t)]
                = inf_t [¬A(t) ∨ B(t)(f t)]
                = ∀t: A(t) = 1 → B(t)(f t) = 1
```

In Boolean, this is:
- 1 if f maps all A-elements to B-elements
- 0 otherwise

This is exactly the standard function type.

### Σ Collapses to Standard Dependent Pair

```
(Σ x:A. B x)(p) = A(fst p) ∧ B(fst p)(snd p)
```

In Boolean:
- 1 if fst p ∈ A and snd p ∈ B(fst p)
- 0 otherwise

This is the standard dependent pair.

### + Collapses to Standard Sum

```
(A + B)(inl a) = A(a)
(A + B)(inr b) = B(b)
```

In Boolean: standard disjoint union.

### Id Collapses to Standard Identity

```
(Id_A a b)(refl) = [a ≡ b] ∧ A(a)
```

In Boolean:
- 1 if a ≡ b and a ∈ A
- 0 otherwise

## Judgments Collapse

The judgment Γ ⊢ t @ c with c ∈ {0, 1} becomes:
```
c = 1:  "t is defined/meaningful in Γ"
c = 0:  "t is undefined/meaningless in Γ"
```

The typing judgment:
```
Γ ⊢ t : A @ 1   iff   t ∈ A and t is defined
Γ ⊢ t : A @ 0   iff   trivially (vacuously)
```

At credence 1, we recover standard typing.
At credence 0, everything is vacuously typed.

## What About Unit and Empty?

### Unit
```
Unit = λt. 1
```

In Boolean, Unit(t) = 1 for all t.
This means EVERY term is in Unit.

Wait, that's too big. We need:
```
Unit = λt. [t ≡ ★]
```

Only the canonical element ★ is in Unit.

### Empty
```
Empty = λt. 0
```

In Boolean, Empty(t) = 0 for all t.
No term is in Empty. Correct!

## The Correspondence Theorem

**Theorem**: Let MLTT be Martin-Löf Type Theory (Π, Σ, +, Id).
Let CredTT[Bool] be CredTT v2 instantiated at Boolean credences.

Then there is an equivalence:
```
MLTT derivations  ≅  CredTT[Bool] derivations at credence 1
```

**Proof sketch**:
- Types in MLTT correspond to Boolean predicates
- Typing judgments correspond to predicate satisfaction
- Type formers correspond to Boolean operations on predicates
- The rules match because Boolean operations satisfy De Morgan laws

## Beyond Boolean: What's New

When C ≠ {0, 1}, we get phenomena that don't exist in MLTT:

### Partial Types
A term can be "partially" in a type:
```
A(t) = 0.7   -- t is 70% in A
```

### Graded Functions
```
(A → B)(f) = 0.8   -- f is 80% a valid function from A to B
```

### Fixed Points
The equation c = ~c has:
- No solution in Boolean
- Solution c = 0.5 in [0,1]

This enables Gödel sentences with intermediate credence.

### Graded Ex Falso
In Boolean: from ⊥ (credence 0), derive anything at credence 1.
In graded: from credence c, derive conclusions at credence c.

Impossibility propagates rather than exploding.

## Summary

| Concept | CredTT v2 | Boolean Collapse (MLTT) |
|---------|-----------|-------------------------|
| Credence | c ∈ C (any algebra) | c ∈ {0, 1} |
| Type | Predicate Term → C | Set of terms |
| Π | inf_t [A(t) ⇒ B(f t)] | Standard function |
| Σ | A(fst) * B(snd) | Standard pair |
| + | Disjunction | Disjoint union |
| Id | Equality test | Standard identity |
| Unit | Constant 1 | Singleton |
| Empty | Constant 0 | Empty set |

**MLTT is not the foundation. It's the Boolean shadow of graded structure.**
