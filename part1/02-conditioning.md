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

## Our Approach (Chain Rule Axiom)

We simplify further:

```
Primitive: (a | b) : C → C → C

Axiom (Chain Rule):
    (a | b) * b = a * b

Derived behavior:
    b = 1: (a | 1) * 1 = a * 1 = a, so (a | 1) = a
    b = 0: (a | 0) * 0 = a * 0 = 0, satisfied for ANY (a | 0)
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
(A | ⊥) * ⊥ = A * ⊥ = ⊥
```
This is satisfied for any (A | ⊥), so we cannot derive (A | ⊥) = 1.

## The Graded Ex Falso Spectrum

As the condition becomes less certain:

| cred(B) | (A \| B) is... |
|---------|----------------|
| 1 | fully determined by chain rule |
| 0.5 | weakly constrained |
| ε (small) | almost unconstrained |
| 0 | completely unconstrained |

Classical logic only sees the endpoints. Cred sees the entire spectrum.

## Prior Art

| Source | Contribution |
|--------|--------------|
| Rényi (1955) | Conditional probability as primitive |
| Popper (1959) | Conditional more fundamental than absolute |
| Markov categories (2020) | Categorical disintegration (no division) |
| **Cred** | Chain rule axiom for logic foundation |
