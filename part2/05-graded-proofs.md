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

## Credence Ranges

| cred(P) | Status |
|---------|--------|
| 1 | Proven (certain) |
| → 1 | Asymptotic proof (converging) |
| (0.5, 1) | Partial evidence (degree of belief) |
| 0.5 | Undecided / undecidable |
| (0, 0.5) | Partial counter-evidence |
| → 0 | Asymptotic refutation |
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
- Current credence: high (degree of belief based on evidence)
- But NOT proven: no convergence to 1 yet

A proof would require cred → 1 (convergence), not just "high credence".

## Proof by Accumulation

In Cred, proofs can work by accumulating evidence:

```
Initial: cred(P) = 0.5 (no information)

Evidence 1: Consistent with P
  cred(P) increases to 0.6

Evidence 2: Another consistency check
  cred(P) increases to 0.7

...

If evidence keeps accumulating and cred → 1: PROOF
If evidence stalls and cred plateaus: partial evidence (not proof)
```

The key: proof requires CONVERGENCE to 1, not just high credence.

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
- "Undecidable (in a proof system)" means: neither P nor ¬P is derivable from the given axioms/rules.

Part 1 does not imply that incompleteness phenomena automatically correspond to the numerical value 0.5. The special value 0.5 is forced by a *self-negation equation* (`c = ~c`), not by “unprovable”.

A reasonable modelling choice for “no evidence either way (so far)” is to set a prior near 0.5, but that is epistemic and contingent; it is not a theorem.

## What Counts as a Proof?

A **proof** is a process where credence CONVERGES to 1:

```
Proof:       cred(P) → 1 (converges to certainty)
Refutation:  cred(P) → 0 (converges to impossibility)
No decision: cred(P) does not converge to 0 or 1 (may plateau at an intermediate value)
```

**Important**: There is no "weak proof at 0.9" or "partial proof at 0.7". Having cred(P) = 0.7 means you have partial evidence — which is meaningful! — but it's not a proof unless it's part of a sequence converging to 1.

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
