# New Proof Techniques in Cred

## Techniques Unique to Graded Logic

Classical logic has: direct proof, contradiction, induction, cases, etc.

Cred adds new techniques that exploit graded credence.

## Technique 1: Credence Bounding

**Idea**: Instead of proving P true/false, bound its credence.

```
Theorem: cred(P) ∈ [0.7, 0.9]

Proof:
- Lower bound: Evidence E₁ implies cred(P) ≥ 0.7
- Upper bound: Counter-evidence E₂ implies cred(P) ≤ 0.9
```

This is useful when exact credence is unknown but bounds are provable.

### Example: Prime Gap Conjecture
```
"There are infinitely many prime gaps ≤ 246"

cred(Conjecture) ∈ [0.99, 1]
Lower bound: Zhang's theorem (gaps ≤ 70,000,000)
Upper bound: Not proven exactly 1
```

## Technique 2: Asymptotic Proof

**Idea**: Show credence approaches 1 as evidence accumulates.

```
Theorem: lim_{n→∞} cred_n(P) = 1

Proof:
- Define evidence sequence E₁, E₂, ...
- Show each Eₙ increases credence
- Show cred_n → 1
```

### Example: Consistency
```
Theorem: lim_{years→∞} cred(Con(ZFC)) = 1

"Proof":
- Each year without contradiction increases credence
- Limit is 1 (though never reached)
```

## Technique 3: Fixed Point Construction

**Idea**: For self-referential statements, find the fixed point.

```
Theorem: cred(S) = 0.5 where S = ~S

Proof:
- S = ~S implies cred(S) = 1 - cred(S)
- Solving: cred(S) = 0.5
```

### Example: Any Liar-like Sentence
```
Theorem: All sentences of form "S ↔ ~φ(S)" have cred = 0.5

Proof: Fixed point of c = 1 - c.
```

## Technique 4: Credence Induction

**Idea**: Prove by induction on credence values, not just natural numbers.

```
Theorem: ∀c ∈ [0,1]. P(c)

Proof by credence induction:
- Base: P(0) and P(1)
- Step: P(c) implies P(c ± ε) for small ε
- Conclusion: P holds for all c ∈ [0,1]
```

This exploits the order structure of [0,1].

## Technique 5: Monotonicity Arguments

**Idea**: Show credence is monotonic in some parameter.

```
Theorem: More evidence E implies higher cred(P)

Proof:
- cred(P | E₁) ≤ cred(P | E₁ ∧ E₂)
- Evidence accumulation is monotonic
```

## Technique 6: Convexity Arguments

**Idea**: Use convexity of credence operations.

```
Multiplication is NOT convex: (a*b + c*d)/2 ≠ ((a+c)/2)*((b+d)/2)

But some operations are, enabling optimization-style proofs.
```

## Technique 7: Limiting Arguments

**Idea**: Take limits in credence space.

```
Theorem: cred(P) = lim_{n→∞} cred(Pₙ)

Where P = lim Pₙ in some appropriate sense.
```

### Example: Infinite Conjunction
```
cred(∀n. P(n)) = inf_n cred(P(n)) = lim_{N→∞} min_{n≤N} cred(P(n))
```

## Technique 8: Robust Proof

**Idea**: Prove P holds even under credence perturbations.

```
Theorem: For all ε-perturbations of premises, cred(P) ≥ 1 - δ

Proof:
- Perturb each premise by ε
- Track credence through derivation
- Bound final credence
```

This gives "robust" theorems that tolerate uncertainty.

## Technique 9: Separation Arguments

**Idea**: Show two statements have separated credences.

```
Theorem: cred(P) and cred(Q) are separated by gap δ

Proof:
- Show cred(P) ≥ c + δ
- Show cred(Q) ≤ c
```

Useful for distinguishing almost-equal credences.

## Technique 10: Conditioning Chains

**Idea**: Build up credence through chains of conditioning.

```
cred(Z) = cred(Z | Y) * cred(Y)
        = cred(Z | Y) * cred(Y | X) * cred(X)
        = ...
```

Chain through intermediate propositions.

## Classical Techniques That Still Work

All classical techniques work when credences are 0 or 1:
- Direct proof: Derive P with cred = 1
- Contradiction: Show ~P leads to cred(⊥) > 0, contradiction
- Induction: As usual
- Cases: Combine cases with cred product/sum
- Contrapositive: Works for conditioning

## Techniques That Change

| Classical | Cred |
|-----------|------|
| Ex falso (from ⊥, anything) | Doesn't work |
| Law of excluded middle | cred(P) + cred(~P) = 1, but P ∨ ~P might have cred < 1 |
| Double negation elimination | Works: ~~c = c |

## Combinations

Real proofs combine techniques:

```
Theorem: cred(Goldbach) ≥ 0.99

Proof:
1. Verification up to 10^18 (asymptotic evidence)
2. Heuristic arguments (credence bounding)
3. Absence of counterexample (monotonicity)
Combined: cred ≥ 0.99
```

## Open Questions

1. What's the proof-theoretic strength of these techniques?
2. Can all classical proofs be translated to Cred proofs?
3. Are there theorems provable in Cred but not classically?
4. What's the computational complexity of Cred proof checking?
