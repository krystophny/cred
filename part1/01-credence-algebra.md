# The Credence Algebra

## Primitives

```
C     : [0, 1]              -- credence values
0     : C                   -- impossibility
1     : C                   -- certainty
*     : C → C → C           -- conjunction (multiplication)
~     : C → C               -- negation (~c = 1 - c)
≤     : C → C → Prop        -- ordering
_|_   : C → C → C           -- conditioning (PRIMITIVE)
```

## Axioms for *, ~, ≤ (De Morgan Algebra)

```
c * 1 = c                           identity
c * 0 = 0                           annihilation
(a * b) * c = a * (b * c)           associativity
a * b = b * a                       commutativity

~0 = 1                              complement bounds
~1 = 0
~~c = c                             involution

c ≤ c                               reflexivity
a ≤ b ∧ b ≤ c → a ≤ c               transitivity
a ≤ b ∧ b ≤ a → a = b               antisymmetry
0 ≤ c ≤ 1                           bounded
```

## Axioms for Conditioning (The Innovation)

```
(a | b) * b = a * b                 chain rule
(a | 1) = a                         certain condition
(a | 0) unconstrained               impossible condition
```

Note: When b = 0, the chain rule becomes:
```
(a | 0) * 0 = a * 0 = 0
```
This is satisfied for ANY value of (a | 0). The conditional is **unconstrained**, not defined to be 1.

## Derived Operations

```
a + b := ~(~a * ~b)                 disjunction (De Morgan dual)
```

Note: We do NOT derive implication as ~a + b. Material implication is NOT part of Cred.

## Comparison

| Operation | Material Implication | Conditioning |
|-----------|---------------------|--------------|
| Definition | A → B := ~A + B | (B \| A) primitive |
| At A = 0 | A → B = 1 | (B \| A) unconstrained |
| Ex falso | ⊥ → C = 1 (anything follows) | (C \| ⊥) = ? (nothing determined) |
| Nature | Truth-functional | Relational (chain rule) |

## Why Product Multiplication?

We use standard multiplication (product t-norm) because:
1. Matches probability: P(A ∧ B) = P(A) · P(B) for independent events
2. Chain rule is probabilistic: P(A,B) = P(A|B) · P(B)
3. Credences compound: uncertainty multiplies

Alternative t-norms (min, Łukasiewicz) don't have this probabilistic interpretation.

## Instances

### Instance 1: Full Graded [0, 1]
```
C = [0, 1]
* = multiplication
~ c = 1 - c
≤ = standard
(a | b) via chain rule
```

### Instance 2: Three-Valued {0, ½, 1}
```
C = {0, ½, 1}
* = multiplication (with ½ * ½ → ½ by convention)
~ c = 1 - c
(a | b) via chain rule
```

### Instance 3: Boolean {0, 1}
```
C = {0, 1}
* = AND
~ = NOT
(a | b) = a when b = 1, unconstrained when b = 0
```
