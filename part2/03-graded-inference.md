# Graded Inference

## Classical Inference

From premises, derive conclusions with certainty:
```
A, A → B ⊢ B    (modus ponens)
```

The conclusion is TRUE if premises are TRUE.

## Graded Inference

From premises with credences, derive conclusions with credences:
```
A @ c₁, (B | A) @ c₂ ⊢ B @ ?
```

How does credence propagate?

## The Chain Rule as Inference

The chain rule:
```
(B | A) * A = A ∧ B
```

As an inference:
```
If cred(A) = c₁ and cred(B | A) = c₂
Then cred(A ∧ B) = c₁ * c₂
```

## Modus Ponens in Cred

Classical: A, A → B ⊢ B

Cred version:
```
cred(A) = c₁
cred(B | A) = c₂
─────────────────
cred(B) ≥ c₁ * c₂
```

Why ≥ instead of =? Because B might have credence from other sources too.

When c₁ = c₂ = 1 (certain premises):
```
cred(A) = 1
cred(B | A) = 1
─────────────────
cred(B) = 1
```

We recover classical modus ponens.

## Conjunction Introduction

```
cred(A) = c₁
cred(B) = c₂
─────────────────
cred(A ∧ B) = c₁ * c₂
```

Credences multiply.

## Conjunction Elimination

```
cred(A ∧ B) = c
─────────────────
cred(A) ≥ c
cred(B) ≥ c
```

## Disjunction Introduction

```
cred(A) = c
─────────────────
cred(A ∨ B) ≥ c
```

## Contrapositive

```
cred(B | A) = c
─────────────────
cred(~A | ~B) = c
```

Contrapositive preserves credence.

## Proof by Contradiction

```
cred(⊥ | ~P) = 1    (assuming ~P leads to contradiction)
─────────────────
cred(P) = 1
```

Why? From chain rule:
```
cred(⊥ | ~P) * cred(~P) = cred(⊥ ∧ ~P) = 0
1 * cred(~P) = 0
cred(~P) = 0
cred(P) = 1
```

## No Ex Falso

We CANNOT derive:
```
cred(⊥) = 1
─────────────────
cred(A) = 1    ✗ INVALID
```

Because cred(A | ⊥) is unconstrained, not 1.

## Credence Bounds

Inference gives bounds, not exact values:
```
cred(A) = 0.7
cred(B | A) = 0.8
─────────────────
cred(B) ∈ [0.56, 1]
```

The lower bound is c₁ * c₂ = 0.56. Upper bound is 1 (B could be certain independently).

## The Inference Judgment

We can write:
```
Γ ⊢ P @ c
```

Meaning: From premises Γ (with their credences), we can derive P with credence at least c.

## Soundness

The inference rules are sound with respect to the credence algebra:
- If premises have their stated credences
- And we apply valid rules
- Then conclusions have at least their derived credences

## Example Derivation

```
Given:
  Rain @ 0.7
  (Wet | Rain) @ 0.9

Derive:
  Rain ∧ Wet @ 0.63    (by chain rule: 0.7 * 0.9)
  Wet @ ≥ 0.63         (by conjunction elimination)
```

## Comparison to Probabilistic Logic

| System | Inference |
|--------|-----------|
| Probabilistic logic | P(conclusion) computed from P(premises) |
| Fuzzy logic | Truth degree computed via t-norms |
| **Cred** | Credence flows via chain rule |

Cred is closest to probabilistic logic but with conditioning as primitive.
