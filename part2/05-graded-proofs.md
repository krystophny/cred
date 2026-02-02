# Graded Proofs

## Classical Proofs

A proof of P is a finite derivation establishing P is TRUE.
- Binary: P is proven or not proven
- Finite: Proof is a finite object
- Absolute: Once proven, always proven

## Graded Proofs

A proof of P is a process that increases cred(P).
- Continuous: P has a credence that can change
- Potentially infinite: Asymptotic approach to 1
- Relative: Credence depends on evidence

## Proof as Credence Increase

```
Before proof attempt: cred(P) = c₀
After proof step:     cred(P) = c₁ > c₀
After more steps:     cred(P) = c₂ > c₁
...
Limit:                cred(P) → c_∞
```

## Degrees of Proof

| cred(P) | Status |
|---------|--------|
| 1 | Proven (certain) |
| (0.5, 1) | Partially proven (likely true) |
| 0.5 | Undecided / undecidable |
| (0, 0.5) | Partially refuted (likely false) |
| 0 | Refuted (impossible) |

## Asymptotic Proof

A proposition is **asymptotically proven** if:
```
lim_{n→∞} cred_n(P) = 1
```

Where cred_n is the credence after n steps of evidence/derivation.

This is WEAKER than classical proof (cred = 1 exactly) but STRONGER than unprovable.

## Example: Goldbach's Conjecture

"Every even number > 2 is the sum of two primes."

Classical status: Unproven (as of 2024)

Cred status:
- Verified for all even numbers up to 4 × 10^18
- Each verification increases credence
- cred(Goldbach) ≈ very high, approaching 1
- But not exactly 1 (no proof)

Cred captures this "almost certainly true but not proven" state.

## Example: P ≠ NP

Classical: Unknown (neither proven nor refuted)

Cred:
- Most experts believe P ≠ NP
- Evidence: separation of complexity classes, oracle results
- cred(P ≠ NP) ≈ 0.9 (high but not certain)
- cred(P = NP) ≈ 0.1

The credence reflects the state of knowledge.

## Proof by Accumulation

In Cred, proofs can work by accumulating evidence:

```
Initial: cred(P) = 0.5 (no information)

Evidence 1: Consistent with P
  cred(P) → 0.6

Evidence 2: Another consistency check
  cred(P) → 0.7

...

Evidence n: Still consistent
  cred(P) → 1 - ε
```

This is like scientific confirmation, not mathematical proof.

## Proof by Derivation

More traditionally, derivation from axioms:

```
Axioms with cred = 1
Apply inference rules (credence flows)
Derived statement has cred = 1
```

When premises have credence 1 and rules preserve credence 1, conclusions have credence 1.

This recovers classical proof as a special case.

## What About Undecidable Statements?

Gödel's incompleteness: Some true statements are unprovable.

In Cred:
- "Unprovable" means: no derivation reaches cred = 1
- "Undecidable" means: cred stays at 0.5
- Gödel sentence G: cred(G) = 0.5 (fixed point)

The undecidability IS the credence being stuck at 0.5.

## Proof Strength

We can compare proof strength:

```
Strong proof: cred(P) = 1 (certain)
Weak proof: cred(P) = 0.9 (highly likely)
Partial proof: cred(P) = 0.7 (more likely than not)
No proof: cred(P) = 0.5 (no information)
Partial refutation: cred(P) = 0.3 (unlikely)
Strong refutation: cred(P) = 0.1 (very unlikely)
Refutation: cred(P) = 0 (impossible)
```

## Constructive Proofs

A constructive proof provides a witness. In Cred:

```
cred(∃x. P(x)) = sup_x cred(P(x))
```

A constructive proof exhibits an x₀ with cred(P(x₀)) = 1.

A non-constructive proof might show sup_x cred(P(x)) = 1 without exhibiting x₀.

## The Role of Time

Classical proofs are timeless. Cred proofs can be temporal:

```
cred_t(P) = credence of P at time t
```

Evidence accumulates over time. Mathematical knowledge grows.

This matches how mathematics actually works: conjectures become theorems (or counterexamples) over time.

## Summary

| Classical | Cred |
|-----------|------|
| Proof establishes truth | Proof increases credence |
| Binary (proven/not) | Continuous [0, 1] |
| Undecidable = stuck | Undecidable = cred 0.5 |
| Timeless | Can be temporal |
| Absolute | Relative to evidence |
