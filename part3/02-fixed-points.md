# Fixed Points and Self-Reference

## The Classical Problem

Self-referential statements cause paradoxes:
- Liar: "This statement is false" — neither true nor false
- Russell: {x | x ∉ x} — contradiction
- Gödel: "This statement is unprovable" — true but unprovable

## The Cred Solution

Self-referential statements find **fixed point credences**.

### The Liar Sentence

L = "This statement is false" = "L is false" = ~L

In Cred:
```
cred(L) = cred(~L) = 1 - cred(L)

Let c = cred(L):
c = 1 - c
2c = 1
c = 0.5
```

The liar sentence has credence **exactly 0.5**.

Not a paradox. A fixed point.

### Russell's Predicate

R = {x | x ∉ x}

Is R ∈ R?
```
R(R) = ~(R(R))

Let c = cred(R ∈ R):
c = 1 - c
c = 0.5
```

Russell's set has credence 0.5 of containing itself.

No paradox. The predicate is well-defined with this credence.

### Gödel's Sentence

G = "G is not provable in system S"

This is trickier because "provable" relates credence to derivability.

Interpretation: cred(G) = credence that G is true.

If G is true: G is unprovable, so cred(G) can't reach 1 via proof.
If G is false: G is provable, but then G would be true. Contradiction in classical logic.

In Cred:
```
cred(G) = 0.5
```

G is "undecidable" — credence exactly 0.5 (fixed point).

## The Fixed Point Theorem

**Theorem**: For any continuous f : [0,1] → [0,1], there exists c ∈ [0,1] with f(c) = c.

**Corollary**: For any self-referential statement S = φ(S) where φ is credence-continuous, there exists a fixed point credence.

## Types of Fixed Points

### Negation Fixed Point
```
c = ~c = 1 - c → c = 0.5
```
Unique fixed point at 0.5.

### Conjunction Fixed Point
```
c = c * c → c = c² → c ∈ {0, 1}
```
Fixed points at 0 and 1.

### Disjunction Fixed Point
```
c = c + c - c² = 2c - c² → c² - c = 0 → c ∈ {0, 1}
```
Fixed points at 0 and 1.

### Conditioning Fixed Point
```
c = (c | c)
Chain rule: (c | c) * c = c * c = c²
If c > 0: (c | c) = c
So c = c is trivially satisfied for any c.
```
All credences are fixed points!

## Stability of Fixed Points

A fixed point c for f is **stable** if nearby values converge to it:
```
|f(c')| < |c' - c| for c' near c
```

For c = ~c:
```
f(c) = 1 - c
f'(c) = -1
|f'(0.5)| = 1 (borderline stable)
```

The negation fixed point at 0.5 is neutrally stable.

## Self-Reference Zoo

| Statement | Equation | Fixed Point |
|-----------|----------|-------------|
| Liar: "I am false" | c = 1-c | 0.5 |
| Truth-teller: "I am true" | c = c | any c |
| Asserter: "I am provable" | c = cred(proof exists) | depends on system |
| Denier: "I am unprovable" | c = 1 - cred(proof exists) | = 0.5 (Gödel) |

## Chains of Self-Reference

```
A = "B is false"
B = "A is false"

cred(A) = 1 - cred(B)
cred(B) = 1 - cred(A)

Substituting: cred(A) = 1 - (1 - cred(A)) = cred(A)

Any value works! But combined:
cred(A) + cred(B) = 1
```

Mutual reference creates constraint, not paradox.

## The Diagonal Lemma in Cred

Gödel's diagonal lemma: For any formula φ(x), there exists G with G ↔ φ(⌜G⌝).

In Cred: G has cred(G) satisfying cred(G) = cred(φ(⌜G⌝)).

This always has a solution (fixed point theorem).

## Paradoxes Dissolved

| Classical | Cred |
|-----------|------|
| Liar paradox | Fixed point at 0.5 |
| Russell paradox | Fixed point at 0.5 |
| Grelling-Nelson | Fixed point at 0.5 |
| Berry paradox | Fixed point at 0.5 |

All semantic paradoxes become fixed point equations with solutions.

## Open Questions

1. Are all self-referential fixed points at 0.5, or can others occur?
2. What's the computational complexity of finding fixed points?
3. Can we characterize which fixed points are "natural" vs "artificial"?
4. How do fixed points interact with the collapse to Boolean?
