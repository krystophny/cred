# Asymptotic Proofs

## The Concept

An **asymptotic proof** of P is a sequence of evidence/derivation steps such that:
```
lim_{n→∞} cred_n(P) = 1
```

The credence approaches 1 but may never exactly reach it.

## Classical Proof vs Asymptotic Proof

| | Classical Proof | Asymptotic Proof |
|--|-----------------|------------------|
| Credence | Exactly 1 | Approaches 1 |
| Length | Finite | Potentially infinite |
| Certainty | Absolute | Limit |
| Status | "Proven" | "Asymptotically proven" |

## Examples

### Example 1: Verification-Based

Goldbach's Conjecture: Every even n > 2 is sum of two primes.

```
Verify n = 4: ✓ (4 = 2+2)     cred increasing
Verify n = 6: ✓ (6 = 3+3)     cred increasing
Verify n = 8: ✓ (8 = 3+5)     cred increasing
...
Verify n = 10^18: ✓           cred very high
...
lim_{n→∞} cred_n = 1
```

Each verification increases credence. The key: we care about CONVERGENCE to 1, not crossing some arbitrary threshold.

### Example 2: Probabilistic Primality

Is N prime? Miller-Rabin test:
```
Round 1: Pass → cred(prime) ≥ 0.75
Round 2: Pass → cred(prime) ≥ 0.9375
Round k: Pass → cred(prime) ≥ 1 - (1/4)^k
```

As k → ∞, cred → 1. The key: this is CONVERGENCE to 1, not hitting an arbitrary threshold like 0.99.

### Example 3: Consistency Proofs

Is ZFC consistent?
```
Year 1: No contradiction found → cred ↑
Year 10: Still no contradiction → cred ↑
Year 100: Mathematics works → cred ↑↑
...
```

We have asymptotic evidence for Con(ZFC), not proof.

## Are Asymptotic Proofs "Real" Proofs?

**Classical view**: No. Proof requires cred = 1 exactly.

**Cred view**: Asymptotic proofs are a distinct category:
- Stronger than "unproven" (cred > 0.5)
- Weaker than "proven" (cred = 1)
- Useful and meaningful

## The Hierarchy

```
cred = 1        Classical proof
cred → 1        Asymptotic proof (converging to certainty)
cred ∈ (0.5,1)  Partial evidence (degree of belief)
cred = 0.5      Undecided (neutral prior)
cred ∈ (0,0.5)  Partial counter-evidence
cred → 0        Asymptotic refutation
cred = 0        Classical refutation
```

Note: Asymptotic proofs are defined by CONVERGENCE to 1, not by crossing an arbitrary threshold.

## Converging to 1

How can cred converge to 1?

**From below**: Each step increases cred
```
cred_0 = 0.5
cred_n = 1 - (1/2)^n
lim cred_n = 1
```

**Monotonically**: Evidence only increases cred
```
cred_0 ≤ cred_1 ≤ cred_2 ≤ ... → 1
```

**Non-monotonically**: Evidence can decrease cred, but limit is 1
```
cred_n oscillates but converges to 1
```

## Asymptotic Proof Techniques

### Exhaustive Verification (Infinite)
For decidable P(n):
```
Verify P(0), P(1), P(2), ...
If all pass: cred(∀n. P(n)) → 1
```

### Probabilistic Amplification
Run randomized test k times:
```
Each pass multiplies error by constant < 1
cred → 1 as k → ∞
```

### Inductive Evidence
```
Base case works: cred ↑
Inductive step works for k cases: cred ↑
...
```

## When Asymptotic Proofs Suffice

In practice, asymptotic proofs are often enough:
- Cryptography: Miller-Rabin primality (cred ≈ 1 - 2^-100)
- Physics: Experimental verification (cred ≈ 1 - ε)
- Engineering: Testing (cred approaches 1 with more tests)

The distinction matters philosophically, less so practically.

## Formalizing Asymptotic Proof

```
AsymptoticProof(P) := ∃(cred_n)_{n∈ℕ}. lim_{n→∞} cred_n(P) = 1

Where cred_n is "credence after n units of evidence"
```

This is a well-defined notion that sits between "proven" and "unproven."

## Open Questions

1. Can we characterize which statements have asymptotic proofs?
2. Is "asymptotically provable" decidable?
3. What's the relationship to probabilistically checkable proofs (PCPs)?
4. Can classical proofs always be converted to asymptotic proofs? (Yes, trivially)
5. Are there statements with asymptotic proofs but no classical proofs?
