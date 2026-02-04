# Valuations: Mapping Propositions to Credences

## What Part 1 provides

Part 1 defines operations on credence *values* in [0,1]:

```
Complement:   ~c = 1 - c
Product:      c1 ⊗ c2 = c1 * c2    (product t-norm)
Disjunction:  c1 ⊔ c2 = ~(~c1 ⊗ ~c2) = c1 + c2 - c1*c2   (De Morgan dual)
Conditioning: condCred ⊗ evidence = joint   (chain rule)
```

These are operations on *numbers*. No propositions appear. The propositional notation `cred(A|B) * cred(B) = cred(A ∧ B)` is mnemonic (Part 1, Remark on Algebraic vs. Interpreted Conditioning).

## What a valuation adds

A *valuation* is a function `v : Prop -> [0,1]` that assigns credences to propositions. This is the interpretation layer that Part 1 deliberately omits.

A valuation connects the propositional world (A, B, A ∧ B, ...) to the algebraic world ([0,1], ⊗, ⊔, ~).

## Valuation constraints

A Cred valuation `v` must respect the complement:

```
v(~A) = ~v(A) = 1 - v(A)
```

Beyond this, different systems impose different constraints:

### Independent valuation (strongest constraint)

```
v(A ∧ B) = v(A) ⊗ v(B)         for all A, B
v(A ∨ B) = v(A) ⊔ v(B)         (follows by De Morgan)
```

This treats all propositions as independent. It makes the valuation a homomorphism from propositions to the algebra. Fuzzy valuations in product logic work this way.

Problem: real propositions are rarely independent. `v(Rain ∧ Rain) = v(Rain)^2 ≠ v(Rain)` because ⊗ is not idempotent (Part 1, Theorem on Idempotence Characterization). So independent valuations cannot handle `A ∧ A = A`.

### Joint-parametrized valuation (weakest constraint)

```
v(A ∧ B) = j(A, B)             (externally supplied joint)
v(A ∨ B) = v(A) + v(B) - j(A,B)   (inclusion-exclusion with actual joint)
```

This is how probability works: the joint is determined by the measure, not by the marginals. Cred allows the same approach without requiring a measure.

The chain rule then relates conditioning to the supplied joint:
```
v(A|B) * v(B) = j(A, B)
```

### What Cred leaves open

Between these extremes, many intermediate positions exist:
- Supply joints only for "basic" propositions, derive the rest
- Assume independence for some pairs but not others
- Constrain joints by Frechet-Hoeffding bounds (Part 1, Proposition on Frechet-Hoeffding Bounds) without pinning exact values

The choice of joint structure is precisely where probability, fuzzy logic, and Cred-based systems diverge.

## Comparison

| System | Valuation target | Joint determined by |
|--------|-----------------|---------------------|
| Classical logic | {0, 1} | Boolean algebra (A ∧ B = min(A,B)) |
| Probability | [0,1] | Measure on sigma-algebra |
| Product fuzzy logic | [0,1] | Product t-norm (independence) |
| Cred | [0,1] | External parameter (chain rule constrains conditioning) |

## Valuations and the collapse

Part 1 establishes a surjective homomorphism `collapse : [0,1] -> {0, 1/2, 1}` to the Kleene lattice, preserving complement, conjunction (product/min), and disjunction (De Morgan dual/max).

Given a Cred valuation `v : Prop -> [0,1]`, composing with the collapse gives a three-valued valuation:

```
v3 = collapse ∘ v : Prop -> {0, 1/2, 1}
```

This is a Kleene valuation. Depending on which values count as "designated" for valid inference, this yields K3 (designate 1), LP (designate 1 and 1/2), or RM3 (designate 1 and 1/2, with relevance condition).

The collapse is the mechanism by which Cred connects to the three standard logics on the Kleene lattice.

## The liar and self-reference

Part 1 shows that the negation equation `c = ~c` has a unique solution at c = 1/2. If a valuation assigns `v(L) = v(~L)`, then `v(L) = 1/2`. The liar sentence is not paradoxical; it has a determinate credence.

Russell's predicate R = {x : x not in x} similarly gives R(R) = 1/2. Unrestricted comprehension does not lead to contradiction; it leads to fixed points.
