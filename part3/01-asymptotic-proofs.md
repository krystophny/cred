# Asymptotic Proofs

## Prerequisites

This file assumes Part 1 (the constraint algebra) and Part 2 (valuations and update rules). It explores what "proof" means when credence is graded.

## The concept

A classical proof establishes that cred(P) = 1 exactly. An **asymptotic proof** is a sequence of updates such that:

```
lim_{n->inf} cred_n(P) = 1
```

The credence converges to 1 but may never exactly reach it.

## How credence changes: the update mechanism

Part 2 defines update rules (Bayesian conditionalization, Jeffrey conditionalization) that prescribe how a valuation changes when new evidence arrives. Asymptotic proof requires specifying:

1. A sequence of evidence events E_1, E_2, ...
2. An update rule (from Part 2)
3. A prior valuation v_0

The sequence of posteriors v_1, v_2, ... determines whether cred converges to 1.

Without an update rule, "credence increases" is not well-defined. The bare algebra (Part 1) provides no mechanism for credence change; it only constrains how credences relate at a single moment.

## Classical proof vs. asymptotic proof

| | Classical proof | Asymptotic proof |
|--|-----------------|------------------|
| Credence | Exactly 1 | Converges to 1 |
| Length | Finite | Potentially infinite |
| Certainty | Absolute | In the limit |
| Mechanism | Derivation from axioms | Sequence of updates |

## Examples

### Probabilistic primality (well-defined)

Is N prime? Miller-Rabin test with update rule:

```
Prior: cred(prime) = 1/2  (uninformative)
Round 1: Pass -> Bayesian update -> cred(prime) >= 3/4
Round 2: Pass -> cred(prime) >= 15/16
Round k: Pass -> cred(prime) >= 1 - (1/4)^k
```

This is well-defined because: (a) the prior is specified, (b) the update is Bayesian conditionalization, (c) convergence to 1 is provable.

### Exhaustive verification (well-defined for decidable properties)

For decidable P(n), verify P(0), P(1), P(2), ...:

```
After verifying P(0)...P(N), all passing:
cred(forall n. P(n)) increases toward 1
```

The update mechanism: each verification is a piece of evidence E_k = "P(k) holds." Bayesian conditionalization on E_k updates the credence of the universal claim. Convergence to 1 depends on the prior and the update rule.

### Consistency of ZFC (not well-defined without more structure)

"Each year without contradiction increases credence" is not a well-defined update because:
- What counts as "evidence" for consistency?
- What prior do we start from?
- What update rule applies?

Formalizing this requires specifying a theory of how mathematical practice provides evidence, which goes beyond Parts 1-2.

## The hierarchy

```
cred = 1        Classical proof (derivation from axioms)
cred -> 1       Asymptotic proof (convergence under updates)
cred in (0,1)   Partial evidence (not converging)
cred = 0        Refutation
```

Asymptotic proof is defined by CONVERGENCE to 1, not by crossing an arbitrary threshold. Having cred = 0.999 is not a proof unless it is part of a sequence converging to 1.

## Convergence patterns

**Monotone from below** (e.g., probabilistic amplification):
```
cred_n = 1 - (1/4)^n -> 1
```

**Non-monotone** (evidence can decrease credence, but limit is 1):
```
cred_n oscillates but converges to 1
```

## Relationship to probabilistically checkable proofs

A PCP provides a classical proof that can be verified probabilistically (with bounded error). In Cred terms: a PCP gives an asymptotic proof with a known convergence rate. The connection is through the update rule: each random check is evidence that updates the credence.

## Open questions

1. Which statements have asymptotic proofs but not classical proofs?
2. For decidable properties, does exhaustive verification always yield convergence? (Depends on the prior and update rule.)
3. Can convergence rates be characterized in terms of the update rule?
4. What is the relationship between asymptotic provability and probabilistic complexity classes (BPP, etc.)?
