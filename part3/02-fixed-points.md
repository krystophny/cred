# Fixed Points and Self-Reference

## What Part 1 establishes

Part 1 proves that the negation equation c = ~c = 1 - c has a unique solution at c = 1/2 (Lean: `neg_fixed_point_unique`). This handles any self-negating statement: the liar sentence, Russell's predicate, Grelling-Nelson, etc.

This file records the broader range of self-referential fixed points.

## Self-negation: the liar and Russell

### The liar sentence

L = "This statement is false" imposes cred(L) = ~cred(L):

```
c = 1 - c  =>  c = 1/2
```

Not a paradox. A fixed point of negation, with unique solution.

### Russell's predicate

R = {x : x not in x} imposes R(R) = ~R(R):

```
c = 1 - c  =>  c = 1/2
```

Russell's predicate has credence 1/2 of containing itself. Unrestricted comprehension yields fixed points, not contradictions (Part 2, graded predicates).

### Grelling-Nelson

"heterological" = "does not describe itself." Self-negating, same equation, c = 1/2.

## Godel sentences are NOT self-negating

G = "G is not provable in system S"

"Not provable" is NOT "false." The liar says L = NOT(L); Godel says G = NOT(Provable(G)). These are structurally different:

- Liar: c = 1 - c (forced to 1/2 by the algebra)
- Godel: relates credence to provability (requires meta-theoretic principles beyond the algebra)

If S is consistent, G is TRUE (in standard models) but unprovable. Assigning cred(G) = 1/2 would be incorrect. See `03-undecidability.md` for the full treatment.

## Types of fixed points

### Negation: c = ~c
```
c = 1 - c  =>  c = 1/2   (unique)
```

### Product: c = c ⊗ c
```
c = c^2  =>  c(c-1) = 0  =>  c in {0, 1}   (two fixed points)
```

This is Part 1's idempotence characterization: the product is idempotent only at the boundary values.

### De Morgan dual: c = c ⊔ c
```
c = 2c - c^2  =>  c^2 - c = 0  =>  c in {0, 1}
```

Same boundary fixed points, by De Morgan duality.

### Conditioning

Conditioning is ternary (Part 1): it relates condCred, evidence, and joint via the chain rule. There is no unary operation "c conditioned on c" without specifying the joint.

If you set evidence = c and joint = c^2, the chain rule gives condCred = c (for c > 0). But this is a tautology about the choice of joint, not a fixed-point phenomenon.

## The general fixed point theorem

**Theorem** (Brouwer): every continuous f : [0,1] -> [0,1] has a fixed point.

For self-referential statements of the form S = phi(S), where phi assigns a credence operation, the fixed point theorem guarantees a solution whenever phi is continuous. The negation fixed point at 1/2 is the simplest case.

## Stability

A fixed point c of f is:
- **Stable** if |f'(c)| < 1 (nearby values converge to c under iteration)
- **Unstable** if |f'(c)| > 1 (nearby values diverge)
- **Neutrally stable** if |f'(c)| = 1

For negation: f(c) = 1 - c, f'(c) = -1, |f'(1/2)| = 1. The negation fixed point is neutrally stable.

For the product: f(c) = c^2, f'(c) = 2c. At c = 0: |f'(0)| = 0 (stable). At c = 1: |f'(1)| = 2 (unstable).

## Chains of mutual reference

```
A = "B is false":  cred(A) = 1 - cred(B)
B = "A is false":  cred(B) = 1 - cred(A)
```

Substituting: cred(A) = 1 - (1 - cred(A)) = cred(A). Any value works, but combined: cred(A) + cred(B) = 1. Mutual reference creates a constraint (anti-correlation), not a paradox.

For longer chains (A says B is false, B says C is false, C says A is false): the system c1 = 1-c2, c2 = 1-c3, c3 = 1-c1 gives c1 = c3, c1 + c2 = 1, yielding a one-parameter family of solutions.

## Self-reference zoo

| Statement | Equation | Fixed points |
|-----------|----------|--------------|
| Liar: "I am false" | c = 1-c | 1/2 (unique) |
| Truth-teller: "I am true" | c = c | any c in [0,1] (trivial) |
| "I am half-true" | c = 1/2 | 1/2 (unique, trivially) |
| "My product with myself is me" | c = c^2 | {0, 1} |

## Open questions

1. Beyond negation, which self-referential operators yield unique interior fixed points? (Product and disjunction only yield boundary fixed points.)
2. For systems of n mutually referencing statements, what is the dimension of the solution set?
3. How do fixed points interact with the collapse to the Kleene lattice? (The collapse maps 1/2 to 1/2, so the liar fixed point is preserved.)
4. Lawvere's fixed point theorem generalizes diagonal arguments categorically. Does it apply to Cred's self-reference?
