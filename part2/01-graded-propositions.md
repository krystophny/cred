# Graded Propositions

## The Classical View

A proposition P is either TRUE or FALSE.
```
P : Bool
P ∈ {0, 1}
```

## The Cred View

We assign a credence to each proposition.
```
cred(P) : C
cred(P) ∈ [0, 1]
```

Interpretation is a choice:
- Epistemic: `cred(P)` is degree of belief.
- Semantic: `cred(P)` is degree of truth.

Part 1 treats Cred as an algebra on `[0,1]` that admits multiple interpretations; graded mathematics is built on top of that algebra.

## Operations on Propositions

Cred defines algebraic operations on credence values. Be careful about what is definitional vs what requires assumptions (e.g. independence, or supplying joint credences).

```
Independence product:  c₁ ⊗ c₂ := c₁ · c₂
De Morgan dual:        c₁ ⊔ c₂ := ~(~c₁ ⊗ ~c₂)
Negation:              ~c := 1 - c

Conditioning (primitive, chain rule constraint):
choose condCred such that  condCred ⊗ cred(Q) = cred(P ∧ Q)
(here `cred(P ∧ Q)` is a joint value, not computed from marginals unless you assume independence)
```

## Examples

```
cred("It will rain") = 0.7
cred("It will be sunny") = 0.3  (note: not necessarily ~rain)
If rain and sunny are independent: cred(rain ∧ sunny) = 0.7 ⊗ 0.3 = 0.21
Conditioning uses the chain rule: cred(rain | cloudy) ⊗ cred(cloudy) = cred(rain ∧ cloudy)
```

## Compound Propositions

```
"If it rains, the ground is wet"
= (wet | rain)

Chain rule: cred(wet | rain) ⊗ cred(rain) = cred(wet ∧ rain)

If cred(rain) = 0.7 and cred(wet ∧ rain) = 0.65:
cred(wet | rain) = 0.65 / 0.7 ≈ 0.93
```

## Tautologies and Contradictions

In classical logic:
- Tautology: always true
- Contradiction: always false

In Cred:
- Tautology: credence 1
- Contradiction: credence 0
- Everything else: credence in (0, 1)

```
spread(c) := c ⊗ ~c = c(1-c)          (max 1/4 at c=1/2)
certainty(c) := c ⊔ ~c = 1 - c(1-c)   (min 3/4 at c=1/2)
```

These are useful derived quantities, but they are not laws like `cred(P ∨ ¬P)=1` or `cred(P ∧ ¬P)=0` unless you add additional semantics connecting the algebra to propositions. In Part 1, `spread` and `certainty` are explicitly treated as algebraic measures on a single credence value, not logical tautologies/contradictions.

## The Liar Sentence

"This sentence is false" = L

Classical: Paradox (neither true nor false)

Cred: L = ~L
```
L = 1 - L
2L = 1
L = 0.5
```

The liar sentence has credence 0.5. Not a paradox, a fixed point.

## Undecidable Propositions

Gödel's G: "This sentence is not provable"

Classical: G is true but unprovable (incompleteness)

Cred does not make incompleteness disappear: Gödel sentences are not self-negating (unprovable is not false). Representing “undecidable” as a stable intermediate credence is a proposal for later work, not a theorem of Part 1.

## Comparison

| Proposition Type | Classical | Cred |
|------------------|-----------|------|
| Tautology | True | 1 |
| Contingent truth | True | (0.5, 1) |
| Undecidable | ??? | (not fixed by Part 1) |
| Contingent falsehood | False | (0, 0.5) |
| Contradiction | False | 0 |

## The Ontological Claim

We are not committed to a single metaphysical reading. Cred can be read epistemically (belief) or semantically (truth degree), and Part 1 is careful to keep the algebra independent of that choice.
