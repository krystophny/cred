# The Credence Algebra

## Primitives

```
C     : [0, 1]              -- credence values
0     : C                   -- impossibility
1     : C                   -- certainty
⊗     : C → C → C           -- independence product (multiplication on values)
~     : C → C               -- negation (~c = 1 - c)
≤     : C → C → Prop        -- ordering
Conditioning(joint, evidence)  -- primitive conditioning relation/structure
```

## Axioms for ⊗, ~, ≤ (De Morgan Algebra)

```
c ⊗ 1 = c                           identity
c ⊗ 0 = 0                           annihilation
(a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)           associativity
a ⊗ b = b ⊗ a                       commutativity

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
condCred ⊗ evidence = joint         chain rule constraint (conditioning)
evidence = 1  ⇒  condCred = joint   certain evidence
evidence = 0  ⇒  joint = 0 and condCred underdetermined
```

Here `evidence` is the credence value `cred(B)` and `joint` is the credence value `cred(A ∧ B)`. Conditioning is not a total function `C × C → C`; it is a relation (or structure) packaging a `condCred ∈ C` together with a proof of the chain rule equation.

Note: When `evidence = 0`, the chain rule becomes:
```
condCred ⊗ 0 = joint
```
This forces `joint = 0` and leaves `condCred` **underdetermined** (any value in `[0,1]` works).

## Derived Operations

```
a ⊔ b := ~(~a ⊗ ~b)                 disjunction (De Morgan dual)
```

Note: We do NOT define implication as ~a ⊔ b. Material implication is NOT part of Cred.

## Comparison

| Operation | Material Implication | Conditioning |
|-----------|---------------------|--------------|
| Definition | A → B := ~A ⊔ B | (B \| A) primitive |
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
Conditioning via chain rule constraint on (joint, evidence)
```

### Instance 2: Three-Valued {0, ½, 1}
```
C = {0, ½, 1}
* = multiplication (with ½ * ½ → ½ by convention)
~ c = 1 - c
Conditioning via chain rule constraint on (joint, evidence)
```

### Instance 3: Boolean {0, 1}
```
C = {0, 1}
* = AND
~ = NOT
Conditioning: condCred * b = joint (so b = 1 ⇒ condCred = joint; b = 0 ⇒ joint = 0 and condCred underdetermined)
```
