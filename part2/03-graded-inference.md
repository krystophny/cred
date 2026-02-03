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

## What Part 1 Actually Provides

Part 1 formalizes an algebra on `[0,1]` plus a primitive conditioning relation constrained by the chain rule:

```
cred(B|A) ⊗ cred(A) = cred(B ∧ A)
```

Here `cred(B ∧ A)` is a **joint** credence value. It is not generally computable from `cred(A)` and `cred(B)` (dependence is real; joint information is additional data).

So, even if you know the numbers `cred(A)=c₁` and `cred(B|A)=c₂`, the chain rule only lets you infer the joint:

```
cred(B ∧ A) = c₂ ⊗ c₁
```

That is already valuable: it tells you what your joint commitments must be if you claim those conditionals and that evidence.

## Why This Is Not Yet a Proof Calculus

To go from a joint credence `cred(A ∧ B)` to a marginal credence `cred(B)` you need additional **structural principles** (e.g. some monotonicity principle expressing that `A ∧ B` should not be more credible than `B`). Part 1 deliberately does **not** postulate such a bridge, because it is precisely where “logic” (about propositions) enters, and it is easy to smuggle in classical explosion by accident.

In particular, statements like
- “`cred(B) ≥ cred(A ∧ B)`”
- “`cred(A ∧ B) = cred(A) ⊗ cred(B)`”
- “Contrapositive preserves conditional credence”

are not consequences of the Part 1 algebra alone; they require extra semantics connecting propositions and the algebra.

## A Conservative Reading (Constraint-First)

One safe way to think about “inference” in Cred is:
- inference introduces **constraints** relating credence values (including joints),
- and additional information (models, priors, or further principles) is needed to extract a single derived number.

This is aligned with the Part 1 philosophy: inference narrows possibilities rather than producing explosion.

## Future Work (Part 2 Proper)

Part 2 is where we will specify (and then justify) extra principles that connect:
- proposition-level connectives (`∧`, `∨`, `¬`) and entailment,
- to the value-level algebra (`⊗`, `⊔`, `~`) and to conditioning constraints.

The goal is to end up with a bona fide, Lean-checked notion of “graded proof” that:
- agrees with classical proofs in the `{0,1}` collapse only when the *extra classical principles* are explicitly assumed,
- but otherwise treats impossible evidence and contradiction as constraint-silent cases (no ex falso).

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
