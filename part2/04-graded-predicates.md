# Graded Predicates and Quantifiers

## From propositions to predicates

A Cred valuation assigns credences to propositions. A *graded predicate* extends this to properties that vary over a domain:

```
P : X -> [0,1]
P(x) = credence that x has property P
```

This is the Cred analogue of a predicate in first-order logic, or equivalently, a fuzzy set.

Crisp predicates (range {0, 1}) are the special case corresponding to classical sets.

## Pointwise operations

The Cred algebra extends pointwise to predicates over any domain X:

```
Complement:    (~P)(x) = 1 - P(x)
Product:       (P ⊗ Q)(x) = P(x) * Q(x)
De Morgan dual: (P ⊔ Q)(x) = P(x) + Q(x) - P(x)*Q(x)
```

These are the same operations as Part 1, applied at each point.

The same caveats apply: P ⊗ Q is the pointwise product, not the joint predicate for dependent properties. For dependent predicates, the joint J(x) = cred(P(x) ∧ Q(x)) must be supplied separately, just as in Part 1.

## Conditioning on predicates

Given:
- Evidence predicate E : X -> [0,1]
- Joint predicate J : X -> [0,1] (with J(x) <= E(x) for all x)

A conditional predicate K : X -> [0,1] satisfies the chain rule pointwise:

```
K(x) * E(x) = J(x)
```

When E(x) > 0: K(x) = J(x) / E(x) (unique).
When E(x) = 0: K(x) is unconstrained (any value works).

This is Part 1's conditioning applied at each point of the domain.

## Quantifiers

### Universal quantifier (infimum)

```
cred(forall x. P(x)) = inf_{x in X} P(x)
```

The universal claim has the credence of the weakest instance.

### Existential quantifier (supremum)

```
cred(exists x. P(x)) = sup_{x in X} P(x)
```

The existential claim has the credence of the strongest instance.

### Why inf/sup

These are the only choices that:
1. Agree with classical quantifiers on crisp predicates (inf over {0,1} = "all true"; sup over {0,1} = "some true")
2. Satisfy quantifier duality: ~(forall x. P(x)) = exists x. ~P(x), since 1 - inf P(x) = sup (1 - P(x))

The product t-norm is used for finitary conjunction (⊗); inf/sup are used for infinitary conjunction/disjunction (quantifiers). This is the same split as in product fuzzy logic.

### Bounded quantifiers

Quantification restricted to elements with positive evidence:

```
cred(forall x in S. P(x)) = inf_{x : S(x) > 0} P(x)
```

Only elements with positive membership in S contribute. Elements with S(x) = 0 are irrelevant (no constraint from zero evidence, consistent with Part 1's conditioning at zero).

### Nested quantifiers

```
cred(forall x. exists y. R(x,y)) = inf_x (sup_y R(x,y))
cred(exists x. forall y. R(x,y)) = sup_x (inf_y R(x,y))
```

The standard inequality holds: sup_x inf_y <= inf_x sup_y.

## Comprehension

In Cred, unrestricted comprehension is available without paradox:

```
{x | phi(x)} is the predicate x -> phi(x)
```

For any phi assigning credences, this defines a valid predicate. Self-referential predicates yield fixed points rather than contradictions:

```
Russell's predicate: R(x) = ~(x(x))
R(R) = ~(R(R)) = 1 - R(R)
So R(R) = 1/2
```

Russell's predicate has credence 1/2 of containing itself. This is a consequence of Part 1's fixed-point result: the negation equation c = 1-c has a unique solution at 1/2.

## Comparison to fuzzy sets

| Aspect | Fuzzy sets | Cred predicates |
|--------|-----------|-----------------|
| Conjunction | min (Godel) or product (product logic) | Product (product t-norm) |
| Disjunction | max or probabilistic sum | De Morgan dual of product |
| Complement | 1 - x | 1 - x (same) |
| Implication | Residuated (forced by t-norm) | Chain rule (unconstrained at zero) |
| Quantifiers | inf/sup | inf/sup (same) |
| Self-reference | Paradoxical or ad hoc | Fixed points from the algebra |
| Joint | Determined by t-norm | External parameter |

The key difference: in fuzzy logic, conjunction determines the joint of any two predicates. In Cred, the joint is separate data, and the product is the t-norm for algebraic operations on values.
