# Update Rules: How Beliefs Change with Evidence

## What Part 1 provides

The chain rule is a *static* constraint:

```
cred(A|B) * cred(B) = cred(A ∧ B)
```

It says how conditional, marginal, and joint credences must relate to each other at a single moment. It says nothing about what happens *when new evidence arrives*.

Part 1 explicitly notes that Cred has no update rule (Part 1, Scope and Limitations). This is the third missing layer.

## What an update rule adds

An update rule prescribes how to revise your entire credence function when you receive new information. Given:

- a prior valuation `v : Prop -> [0,1]`
- new evidence E (learned to be true, or learned to have some credence)

the update rule produces a posterior valuation `v' : Prop -> [0,1]`.

## Bayesian conditionalization

The simplest update rule: when you learn that B is certain, set your new credence in A to your old conditional credence.

```
v'(A) = v(A|B)
```

where v(A|B) is determined by the chain rule: v(A|B) * v(B) = v(A ∧ B), giving v(A|B) = v(A ∧ B) / v(B) when v(B) > 0.

### What makes this an update rule, not the chain rule

The chain rule says: *given* values for joint and evidence, the conditional is constrained. It is atemporal.

Conditionalization says: *when you learn B*, replace your credence function with the conditional-on-B function. It is temporal and prescriptive.

The chain rule is Part 1 (algebra). Conditionalization is Part 2 (reasoning).

### Requirements

Bayesian conditionalization requires:
1. A prior valuation v with v(B) > 0
2. Joint credences v(A ∧ B) for all A (i.e., a fully specified joint structure)
3. The assumption that B is learned with certainty

Requirement 2 is where probability diverges from bare Cred: probability supplies all joints via the measure. Without a measure, the joints must be supplied some other way.

### What happens at v(B) = 0

If v(B) = 0, the chain rule is satisfied by any v(A|B) (Part 1, Theorem on conditioning at zero). The conditional is unconstrained, so conditionalization has no well-defined output.

In probability, this is handled by disintegration (regular conditional probability), which uses measure-theoretic structure to resolve the ambiguity. Cred does not have this structure: conditioning at zero is genuinely unconstrained.

This means: Bayesian conditionalization is available on Cred valuations *only when the evidence has positive credence*. Learning something you previously assigned credence zero to requires a different mechanism (or additional structure).

## Jeffrey conditionalization

Jeffrey (1965) generalized Bayesian conditionalization to uncertain evidence. Instead of learning B with certainty, you learn that B has some new credence q (not necessarily 1):

```
v'(A) = v(A|B) * q + v(A|~B) * (1-q)
```

This is a weighted mixture of the conditional-on-B and conditional-on-not-B valuations.

### Compatibility with Cred

Jeffrey conditionalization requires:
1. Conditionals v(A|B) and v(A|~B)
2. Both determined by the chain rule (requiring joint credences)
3. The new credence q for B

When v(B) > 0 and v(~B) > 0, both conditionals are determined by Part 1's chain rule. Jeffrey conditionalization is available.

When v(B) = 0: v(A|B) is unconstrained, so the Jeffrey update is underdetermined. Again, conditioning at zero provides no constraint.

## The chain rule as constraint on updates

While the chain rule does not prescribe an update rule, it *constrains* what updates are coherent.

If you perform an update v -> v', the new valuation must still satisfy the chain rule:

```
v'(A|B) * v'(B) = v'(A ∧ B)
```

Any update rule must produce a posterior that is itself a valid Cred valuation with consistent joints and conditionals.

### Bayes consistency as a constraint on updates

Part 1's Bayes consistency criterion (the chain rule from both directions) constrains updates further:

```
v(A|B) * v(B) = v(A ∧ B) = v(B|A) * v(A)
```

If an update changes v(B) but keeps the joint structure coherent, Bayes consistency ensures the conditionals remain symmetric.

## What the algebra forces, what it leaves open

| Aspect | Part 1 (algebra) | Part 2 (update rules) |
|--------|------------------|-----------------------|
| Chain rule | Static constraint | Must be preserved after update |
| Division at positive evidence | Unique conditional | Bayesian conditionalization is available |
| Zero evidence | Unconstrained | Update is underdetermined |
| Symmetry (Bayes consistency) | Selects product residuated arrow | Constrains joint structure across updates |
| Which update rule to use | Not specified | A design choice: Bayesian, Jeffrey, or other |

## Comparison of update rules

| Update rule | Evidence type | Requirements beyond Cred | Handles zero evidence? |
|-------------|---------------|--------------------------|----------------------|
| Bayesian conditionalization | B learned with certainty | Full joint structure, v(B) > 0 | No |
| Jeffrey conditionalization | B gets new credence q | Full joint structure, v(B) > 0, v(~B) > 0 | No |
| Probability (disintegration) | B learned with certainty | Measure space, sigma-algebra | Yes (via measure theory) |

Cred provides the algebraic substrate for all these rules. None is forced; each requires additional structure.

## Toward a Cred update rule

An open question: is there a natural update rule for Cred that does not require full probability-theoretic structure but handles more cases than Bayesian conditionalization?

Candidates:
- **Constraint propagation**: when new information arrives, propagate chain-rule constraints through the joint structure without committing to a single posterior
- **Interval-valued updating**: when conditioning at zero, report the full interval [0,1] rather than a single value (connecting to imprecise probability)
- **Copula-based updating**: use the copula framework (Part 1, Remark on Copula Connection) to specify joint structure and derive updates
