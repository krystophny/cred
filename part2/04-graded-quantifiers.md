# Graded Quantifiers

## Classical Quantifiers

```
∀x. P(x) = TRUE iff P(x) is true for all x
∃x. P(x) = TRUE iff P(x) is true for some x
```

## Graded Quantifiers

For a predicate P : X → [0, 1]:

**Universal quantifier (infimum)**:
```
cred(∀x. P(x)) := inf_{x ∈ X} P(x)
```

The "for all" has credence equal to the minimum credence over all instances.

**Existential quantifier (supremum)**:
```
cred(∃x. P(x)) := sup_{x ∈ X} P(x)
```

The "there exists" has credence equal to the maximum credence over all instances.

## Why inf/sup?

**Universal**: "All swans are white"
- If one swan has whiteness 0.3, the universal claim can't exceed 0.3
- The weakest link determines the chain's strength

**Existential**: "Some swan is white"
- If any swan has whiteness 0.9, the existential claim is at least 0.9
- The strongest instance determines existence

## Examples

**"All natural numbers are even"**
```
Even : ℕ → [0, 1]
Even(0) = 1, Even(1) = 0, Even(2) = 1, ...

cred(∀n. Even(n)) = inf{1, 0, 1, 0, ...} = 0
```

**"Some natural number is even"**
```
cred(∃n. Even(n)) = sup{1, 0, 1, 0, ...} = 1
```

**"All real numbers are close to 0"**
```
CloseToZero : ℝ → [0, 1]
CloseToZero(x) = e^(-x²)

cred(∀x. CloseToZero(x)) = inf_{x ∈ ℝ} e^(-x²) = 0
```

**"Most numbers are positive"** (informal)
```
This requires a measure/probability, not just inf/sup.
See below for "most" quantifier.
```

## Bounded Quantifiers

Often more useful:
```
cred(∀x ∈ S. P(x)) := inf_{x : S(x) > 0} P(x)
```

Quantify only over elements with positive membership in S.

## The "Most" Quantifier

Classical logic has ∀ (all) and ∃ (some). Cred can express intermediate:

```
cred(Most x. P(x)) := ∫ P(x) dμ(x) / ∫ dμ(x)
```

This requires a measure μ on the domain. It's the average credence.

## Quantifier Duality

In classical logic: ~∀x.P(x) ↔ ∃x.~P(x)

In Cred:
```
~(inf_x P(x)) = sup_x (~P(x))
1 - inf_x P(x) = sup_x (1 - P(x))
```

This holds! The duality is preserved.

## Nested Quantifiers

```
cred(∀x.∃y. R(x,y)) = inf_x (sup_y R(x,y))
cred(∃x.∀y. R(x,y)) = sup_x (inf_y R(x,y))
```

Note: inf_x sup_y ≥ sup_x inf_y (always)

So ∃x.∀y implies ∀x.∃y (in terms of credence ordering).

## Quantifiers and Conditioning

Conditional universal:
```
cred(∀x. (P(x) | Q(x))) = inf_x cred(P(x) | Q(x))
```

This is: "For all x, P given Q."

## Issues with Infinite Domains

For infinite domains:
- inf may not be achieved (approach but never reach)
- sup may not be achieved
- Need completeness of [0,1] (which we have)

Example:
```
P(n) = 1 - 1/(n+1)  for n ∈ ℕ
P(0) = 0, P(1) = 0.5, P(2) = 0.67, ...

inf_n P(n) = 0      (achieved at n=0)
sup_n P(n) = 1      (limit, not achieved)

cred(∀n. P(n)) = 0
cred(∃n. P(n)) = 1
```

## Comparison to Fuzzy Logic

| System | ∀ | ∃ |
|--------|---|---|
| Classical | All true | Some true |
| Fuzzy | inf (Gödel) or Π (product) | sup (Gödel) or Σ (sum) |
| **Cred** | inf | sup |

We use inf/sup like Gödel fuzzy logic, but with product conjunction.

## First-Order Cred

Combining graded propositions, predicates, inference, and quantifiers:

```
Γ ⊢ ∀x. P(x) @ c    means    inf_x cred(P(x)) ≥ c
Γ ⊢ ∃x. P(x) @ c    means    sup_x cred(P(x)) ≥ c
```

This gives a graded first-order logic (relevant, not classical).
