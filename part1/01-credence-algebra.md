# The Credence Algebra

## Primitives

```
C     : [0, 1]              -- credence values
0     : C                   -- impossibility
1     : C                   -- certainty
⊗     : C → C → C           -- product on credence values (multiplication on values)
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

Here `evidence` is the credence value `cred(B)` and `joint` is the credence value `cred(A ∧ B)`.
Conditioning is **not** a total function `C × C → C`:
- at the **value level** it is a structure `Conditioning(joint, evidence)` that packages a witness `condCred ∈ C` together with a proof of the chain rule constraint `condCred ⊗ evidence = joint`;
- at the **propositional level** we write `cred(A | B)` informally, but the primitive constraint is
  `cred(A | B) ⊗ cred(B) = cred(A ∧ B)`, where `cred(A ∧ B)` is a joint credence supplied as data (not computed from marginals in general).

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
| Definition | A → B := ~A ⊔ B | (A \| B) primitive |
| At evidence = 0 | 0 → B = 1 | (A \| 0) unconstrained |
| Ex falso | ⊥ → C = 1 (anything follows) | (C \| ⊥) = ? (nothing determined) |
| Nature | Truth-functional | Relational (chain rule) |

## Why Product Multiplication?

We use standard multiplication (product t-norm) because:
1. Matches probability: P(A ∧ B) = P(A) · P(B) for independent events
2. Chain rule is probabilistic: P(A,B) = P(A|B) · P(B)
3. Credences compound: uncertainty multiplies

But note: ⊗ is an operation on credence values; it does not, in general, compute joint credence from marginals for dependent propositions.

Alternative t-norms (min, Łukasiewicz) don't have this probabilistic interpretation.

## Instances

### Instance 1: Full Graded [0, 1]
```
C = [0, 1]
⊗ = multiplication (on values)
~ c = 1 - c
≤ = standard
Conditioning via chain rule constraint on (joint, evidence)
```

### Instance 2: Three-Valued {0, ½, 1}
```
C = {0, ½, 1}
⊗, ⊔, ~ are the RM3-style operations on the three values (Lean: `ThreeVal.conj`, `ThreeVal.disj`, `ThreeVal.neg`).
This three-valued algebra can be obtained from the full [0,1] algebra by a collapse that maps 0 ↦ 0, 1 ↦ 1, and (0,1) ↦ ½.
Conditioning is still primitive via the chain rule constraint on (joint, evidence).
```

### Instance 3: Boolean {0, 1}
```
C = {0, 1}
⊗ = AND
~ = NOT
Conditioning: condCred ⊗ b = joint (so b = 1 ⇒ condCred = joint; b = 0 ⇒ joint = 0 and condCred underdetermined)
```
