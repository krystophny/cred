# Fixed Points and Self-Reference

## The Classical Problem

Self-referential statements cause issues in binary logic:
- Liar: "This statement is false" — self-negating, neither consistently true nor false
- Russell: {x | x not in x} — self-negating membership, contradiction

## The Cred Solution

Self-NEGATING statements find fixed point credences via the negation operator.

### The Liar Sentence

L = "This statement is false" = "L is false" = NOT L

In Cred:
```
cred(L) = cred(NOT L) = 1 - cred(L)

Let c = cred(L):
c = 1 - c
2c = 1
c = 0.5
```

The liar sentence has credence **exactly 0.5**.

Not a paradox. A fixed point of negation.

### Russell's Predicate

R = {x | x not in x}

Is R in R?
```
R(R) = NOT(R(R))

Let c = cred(R in R):
c = 1 - c
c = 0.5
```

Russell's set has credence 0.5 of containing itself.

The predicate is self-negating, so it gets the negation fixed point.

### Important: Godel Sentences are Different

G = "G is not provable in system S"

This is fundamentally different from the liar. "Not provable" is NOT "false."

- Liar: L means NOT L (self-negating: c = 1-c)
- Godel: G means NOT(Provable(G)) (NOT self-negating)

If S is consistent, Godel showed G is TRUE (in standard models) but unprovable.
Assigning cred(G) = 0.5 would be incorrect; G has a definite truth value.

**Cred handles self-negation. Godel's incompleteness concerns provability in formal systems and applies to Cred if extended to express arithmetic.**

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
Conditioning depends on a *joint* parameter; it is not a unary operation `f(c)`.

If you choose evidence `= c` and joint `= c²`, then the chain rule forces
`(c | c) = c` when `c > 0`. This is a tautology about how you chose the joint,
not a new fixed-point phenomenon.
```
So: “conditioning fixed points” is not a meaningful notion without fixing how joint values are supplied.

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
| Liar: "I am false" | c = 1-c | 0.5 (negation fixed point) |
| Truth-teller: "I am true" | c = c | any c (trivial identity) |
| "I imply myself" | c = cred(c -> c) = 1 | 1 |

Note: Statements involving "provable" are NOT self-negating in the same way as the liar. Godel sentences have definite truth values in standard models.

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

## Self-Negating Paradoxes Resolved

| Classical | Cred |
|-----------|------|
| Liar paradox | Negation fixed point at 0.5 |
| Russell paradox | Negation fixed point at 0.5 |
| Grelling-Nelson | Negation fixed point at 0.5 |

Self-NEGATING paradoxes (where X = NOT X) have the unique solution cred = 0.5.

Note: Not all "paradoxes" are self-negating. Berry's paradox involves definability, not simple self-negation. Godel's theorem involves provability. These require more careful analysis.

## Open Questions

1. Are all self-referential fixed points at 0.5, or can others occur?
2. What's the computational complexity of finding fixed points?
3. Can we characterize which fixed points are "natural" vs "artificial"?
4. How do fixed points interact with the collapse to Boolean?
