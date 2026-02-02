# Graded Propositions

## The Classical View

A proposition P is either TRUE or FALSE.
```
P : Bool
P ∈ {0, 1}
```

## The Cred View

A proposition P IS its credence.
```
P : C
P ∈ [0, 1]
```

A proposition isn't something that HAS a credence. A proposition IS a credence value.

## Operations on Propositions

Since propositions are credences, operations are credence operations:

```
P AND Q := P * Q              multiplication
P OR Q  := P + Q := ~(~P * ~Q)   De Morgan dual
NOT P   := ~P := 1 - P        complement
P GIVEN Q := (P | Q)          conditioning (primitive)
```

## Examples

```
"It will rain" = 0.7
"It will be sunny" = 0.3  (note: not necessarily ~rain)
"Rain AND sunny" = 0.7 * 0.3 = 0.21  (if independent)
"Rain GIVEN cloudy" = (rain | cloudy) via chain rule
```

## Compound Propositions

```
"If it rains, the ground is wet"
= (wet | rain)

Chain rule: (wet | rain) * rain = rain AND wet

If rain = 0.7 and rain AND wet = 0.65:
(wet | rain) = 0.65 / 0.7 ≈ 0.93
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
"P OR NOT P" = P + ~P = P + (1 - P) = 1  (tautology, but only for OR)

"P AND NOT P" = P * ~P = P * (1 - P)
Maximum at P = 0.5: 0.5 * 0.5 = 0.25
```

Note: Contradictions have credence at most 0.25, not 0!

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

Cred: G has credence ≈ 0.5
- Not provable (credence doesn't reach 1)
- Not refutable (credence doesn't reach 0)
- The undecidability IS the credence 0.5

## Comparison

| Proposition Type | Classical | Cred |
|------------------|-----------|------|
| Tautology | True | 1 |
| Contingent truth | True | (0.5, 1) |
| Undecidable | ??? | 0.5 |
| Contingent falsehood | False | (0, 0.5) |
| Contradiction | False | [0, 0.25] |

## The Ontological Claim

We're not saying "propositions have degrees of truth" (that's fuzzy logic framing).

We're saying "a proposition IS a credence value." There's no underlying Boolean truth that we're uncertain about. The credence IS the reality.

This is analogous to quantum mechanics: the wave function isn't uncertainty about a hidden state; the wave function IS the state.
