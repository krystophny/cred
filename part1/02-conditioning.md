# Conditioning: Chain Rule vs Division

## The Standard Approach (Division)

In probability theory, conditioning is typically DEFINED via division:

```
P(A | B) := P(A ∧ B) / P(B)     when P(B) > 0
P(A | B) := undefined           when P(B) = 0
```

Problems:
1. Requires division (more structure than multiplication)
2. Undefined at zero (partial operation)
3. Doesn't clearly separate the CONCEPT from its COMPUTATION

## The Rényi Approach (Primitive)

Rényi (1955) axiomatized conditioning as PRIMITIVE:

```
(A | B) is a primitive operation

Axioms:
1. (A | B) ≥ 0
2. (B | B) = 1
3. (A₁ ∪ A₂ | B) = (A₁ | B) + (A₂ | B)   for disjoint A₁, A₂
4. (A ∧ B | C) = (A | B ∧ C) · (B | C)    CHAIN RULE
```

No division anywhere.

## Our Approach (Chain Rule Constraint)

We simplify further, and we are explicit about the type of object we are postulating.

```
Conditioning is primitive, but it is NOT a total function C × C → C.

At the level of credence values, we model conditioning as a relation/structure:

Given:
  evidence ∈ C   (think: cred(B))
  joint    ∈ C   (think: cred(A ∧ B))

a conditioning witness is a value condCred ∈ C such that:
  condCred ⊗ evidence = joint

(Lean: `Cred.Credence.Conditioning joint evidence` packages `condCred` together
with a proof of this equation.)

Derived behavior (as equations, not vibes):
  evidence = 1:  condCred = joint
  evidence = 0:  possible iff joint = 0; then any condCred works (underdetermined)
  evidence > 0 and joint ≤ evidence: condCred = joint / evidence (unique)
```

## What Happens at Zero?

| Approach | At b = 0 |
|----------|----------|
| Division | P(A \| B) = 0/0 = undefined |
| Material implication | A → B = ~A + B = 1 (ex falso) |
| **Chain rule** | (A \| 0) unconstrained |

The chain rule gives a THIRD option: not undefined, not definitely true, but **unconstrained**.

## Why "Unconstrained" Is Right

When the condition is impossible:
- You can't determine what would follow
- But you also can't assert nothing follows
- The conditional relationship simply has no constraint

This matches intuition:
- "If 2+2=5, then pigs fly" — not true, not false, just... unconstrained
- "If I were a billionaire, I'd buy an island" — counterfactual, not truth-functional

## Connection to Relevant Logic

Relevant logic (Anderson & Belnap) rejects ex falso:
```
⊥ → A is NOT a theorem
```

They enforce this via syntactic "relevance" conditions (variable sharing).

We get the same result SEMANTICALLY via the chain rule:
```
cred(A | ⊥) ⊗ 0 = 0
```
This is satisfied for any value of `cred(A | ⊥)` (provided the joint is 0), so we cannot derive `cred(A | ⊥) = 1`.

## The Graded Ex Falso Spectrum

As the evidence credence becomes small, the chain rule makes conditioning computationally inert:

| cred(B) | effect on joint `cred(A ∧ B)` |
|---------|-------------------------------|
| 1 | `cred(A ∧ B) = cred(A|B)` |
| 0.5 | `cred(A ∧ B) = 0.5 ⊗ cred(A|B)` (bounded impact) |
| ε (small) | `cred(A ∧ B) = ε ⊗ cred(A|B)` (tiny impact) |
| 0 | `cred(A ∧ B) = 0` (and `cred(A|B)` is underdetermined) |

Classical logic only sees the endpoints. Cred sees the entire spectrum.

## Prior Art

| Source | Contribution |
|--------|--------------|
| Rényi (1955) | Conditional probability as primitive |
| Popper (1959) | Conditional more fundamental than absolute |
| Markov categories (2020) | Categorical disintegration (no division) |
| **Cred** | Chain rule constraint as primitive conditioning (underdetermined at 0) |
