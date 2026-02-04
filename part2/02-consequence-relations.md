# Consequence Relations: When Does A Entail B?

## What Part 1 provides

Part 1 establishes Cred as an algebra with no consequence relation. It cannot express "A entails B." The collapse homomorphism connects Cred to K3, LP, and RM3, which share the same algebra but differ in their consequence relations.

A consequence relation is the second missing layer.

## What a consequence relation adds

A consequence relation `|-` determines which inferences are valid:

```
A1, A2, ..., An |- B
```

means: if the premises hold, then the conclusion holds. "Hold" requires specifying which credence values count as *designated* (accepted as "holding").

## The three standard choices

The Kleene lattice {0, 1/2, 1} admits three standard consequence relations, differing only in designated values:

### K3: designate {1}

A premise "holds" only at credence 1 (certainty). Consequence:

```
A1, ..., An |-(K3) B  iff  every Kleene valuation making all Ai = 1 also makes B = 1
```

K3 is paracomplete: neither `A |- A ∨ ~A` nor `~A |- A ∨ ~A` holds when A = 1/2, so the law of excluded middle fails. No formula is a K3 tautology.

### LP: designate {1, 1/2}

A premise "holds" at credence 1 or 1/2. Consequence:

```
A1, ..., An |-(LP) B  iff  every Kleene valuation making all Ai >= 1/2 also makes B >= 1/2
```

LP is paraconsistent: A and ~A can both "hold" (at 1/2) without everything following. The law of excluded middle holds (A ⊔ ~A >= 1/2 always), but explosion fails.

### RM3: designate {1, 1/2} with relevance

Like LP but with an additional relevance condition: the premises must share propositional variables with the conclusion. This blocks irrelevant inferences.

## Consequence relations and Cred

On the full [0,1], analogous choices are available:

### Strict consequence (K3-like)

```
A1, ..., An |-(strict) B  iff  every Cred valuation with all v(Ai) = 1 has v(B) = 1
```

Only certainty propagates. This is the strictest option.

### Tolerant consequence (LP-like)

```
A1, ..., An |-(tolerant) B  iff  every Cred valuation with all v(Ai) >= 1/2 has v(B) >= 1/2
```

Via the collapse, this factors through LP.

### Graded consequence (ordering-based)

A different approach: use the credence ordering directly.

```
A |-(graded, t) B  iff  every Cred valuation with v(A) >= t has v(B) >= t
```

This gives a family of consequence relations parametrized by a threshold t in [0,1].

### Credence-preserving consequence

```
A1, ..., An |- B  iff  v(B) >= f(v(A1), ..., v(An))
```

for some function f. For example, the chain rule gives:

```
If v(B|A) = q and v(A) = p, then v(A ∧ B) = p*q
```

This is a constraint, not an entailment. But combined with a monotonicity principle (v(A ∧ B) <= v(B)), it becomes:

```
v(B) >= v(A ∧ B) = v(B|A) * v(A)
```

This is Adams' probability logic: conditional credence propagates through the product, providing a lower bound.

## The key design question

Part 1's chain rule says that when evidence has credence 0, the conditional is unconstrained. Any consequence relation built on Cred must be compatible with this: impossible premises should not force conclusions.

This rules out consequence relations with explosion (from A and ~A, derive anything), because A and ~A can both have credence 1/2, and no constraint forces v(B) to any particular value.

The question for Part 2: which consequence relations are *compatible* with unconstrained conditioning at zero?

- K3 is compatible (no explosion, paracomplete)
- LP is compatible (no explosion, paraconsistent)
- RM3 is compatible (no explosion, relevance-restricted)
- Classical logic is NOT compatible (has explosion)

## Consequence vs. conditioning

An important distinction:

- **Conditioning** (Part 1): a static constraint relating three values. "If you have joint j and evidence e, then the conditional c satisfies c*e = j."
- **Consequence**: a relation between propositions. "From premises A, conclude B."

Conditioning lives at the value level; consequence lives at the proposition level. Part 2 connects the two: conditioning constrains what consequences are available.

## Adams' probability logic

Adams (1965, 1998) showed that conditional probability propagates a form of "uncertainty" through valid classical inferences: if all premises have probability >= 1-e, then the conclusion has probability >= 1-n*e (for n premises). This is sometimes called the "Adams bound."

Cred's chain rule is compatible with this: since every probability space satisfies Cred's axioms (Part 1), Adams' bounds apply to any Cred valuation that happens to be a probability measure.

The question is whether analogous bounds hold for Cred valuations that are *not* probability measures (i.e., without additivity).
