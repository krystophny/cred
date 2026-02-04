# Building Mathematics on Cred

## Prerequisites

This file assumes Part 1 (the constraint algebra) and Part 2 (valuations, consequence relations, and update rules). It explores what happens when you build mathematical structures on graded foundations.

## The basic setup

A Cred valuation assigns credences in [0,1] to mathematical statements. Classical mathematics is the special case where all statements receive credence 0 or 1.

```
Crisp statement:      cred(2 + 3 = 5) = 1
Crisp falsehood:      cred(2 + 3 = 6) = 0
Conjecture:           cred(Riemann Hypothesis) in (0,1)
Independent:          cred(CH | ZFC) is unconstrained (see Part 3, undecidability)
```

## What stays the same

Basic arithmetic and established theorems are crisp: they have credence 0 or 1. Cred does not change established mathematics; it extends the framework to handle partial confidence.

```
cred(Pythagorean theorem) = 1
cred(Fermat's Last Theorem) = 1    (since Wiles' proof)
cred(2 + 2 = 5) = 0
```

The product t-norm restricted to {0,1} is min (Boolean AND). The De Morgan dual restricted to {0,1} is max (Boolean OR). The complement restricted to {0,1} is classical negation. Classical mathematics is a subalgebra.

## What changes

### Conjectures have credences

Instead of "unknown," a conjecture has a credence reflecting available evidence:

```
cred(Goldbach's conjecture) is high (verified to 4 * 10^18, no counterexample)
cred(P != NP) is high (strong structural evidence, expert consensus)
```

These are not theorems (credence is not 1). They are not unknown (credence is not 1/2). They have meaningful intermediate values based on evidence.

### Independence is unconstrained, not 1/2

A statement independent of a theory T (like CH independent of ZFC) is not forced to credence 1/2. "Independent" means the theory imposes no constraint on the credence. This is analogous to conditioning on zero evidence (Part 1): the chain rule is satisfied by any value, so the conditional is unconstrained.

Setting cred(CH) = 1/2 is a modeling choice (representing ignorance), not a theorem. See Part 3, `03-undecidability.md`.

### Proofs are credence certificates

A proof of P is a derivation establishing cred(P) = 1:
1. Start from axioms (credence 1 by assignment)
2. Apply inference rules that preserve credence 1
3. Reach P with credence 1

This recovers classical proof as a special case. But Cred also allows asymptotic proof (cred -> 1 in the limit). See Part 3, `01-asymptotic-proofs.md`.

## Graded predicates as foundations

Part 2 defines graded predicates P : X -> [0,1]. In a graded foundation:

- "Sets" are crisp predicates (range {0, 1})
- Graded predicates generalize sets, with intermediate membership values
- Unrestricted comprehension yields fixed points, not paradoxes (Russell's predicate has self-membership credence 1/2)

Whether this yields a useful foundation for mathematics depends on which additional principles are adopted (Part 2, consequence relations and quantifiers).

## Open questions

1. Can a useful fragment of set theory be built on graded predicates?
2. What is the graded analogue of the axiom of extensionality?
3. Which classical theorems survive with only partial credence in the axioms?
4. What is the relationship between Cred-based foundations and paraconsistent set theory (Brady, Weber)?
