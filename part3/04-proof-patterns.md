# Proof Patterns in Cred

## What changes from classical proof

Cred is not a logic by itself. Proof in Cred requires additional structure: valuation, consequence relation, update rule, and, for external conditioning, labelled side judgments. This file catalogs proof patterns that are available once that structure is in place.

## Patterns that survive from classical logic

### Direct proof (credence 1 throughout)

Start from axioms with credence 1, apply rules that preserve credence 1, reach the conclusion with credence 1. This is classical proof, unchanged.

### Double negation elimination

~~c = c holds in Cred (Part 1, Lean: `neg_neg`). Unlike intuitionist logic, Cred has no issue with double negation.

### Proof by cases

If P(0) and P(1) and P(c) for all c in (0,1), then P holds for all credences. This is case analysis on the three regions of [0,1], the same structure used in Part 1's collapse homomorphism proofs.

## Patterns that fail

### Ex falso quodlibet

From A and ~A, derive anything. This fails in Cred because:
- A and ~A can both have credence 1/2 (the negation fixed point)
- Conditioning on evidence with credence 0 is unconstrained, not forced to 1
- Threshold consequence has explicit explosion countermodels up to threshold 1/2
- The labelled calculus proves `labelled_no_ex_falso`

### Law of excluded middle (algebraic form)

In Cred: c ⊔ ~c = c + (1-c) - c(1-c) = 1 - c(1-c). This equals 1 only when c in {0,1}. For c in (0,1), the "excluded middle" has credence strictly less than 1. In the Kleene collapse, it maps to 1/2 ⊔ 1/2 = max(1/2, 1/2) = 1/2, confirming that it is not designated in K3 (which requires 1).

## Patterns specific to Cred

### Fixed point construction

For self-referential statements S = phi(S), find the fixed point of phi on [0,1]. Part 1 handles the simplest case (negation: c = 1/2). More complex self-referential operators may have multiple fixed points; Brouwer's theorem guarantees at least one for continuous phi.

### Conditioning chains

The chain rule factors joint credences:

```
cred(A ∧ B) = cred(A|B) * cred(B)
cred(A ∧ B ∧ C) = cred(A|B ∧ C) * cred(B|C) * cred(C)
```

This computes **joints** from conditionals and marginals. Turning joints into marginals (getting cred(A) from cred(A ∧ B)) requires additional structure: a Cred analogue of marginalization or total probability, which is not part of Part 1.

### Frechet bounding

Part 1 establishes Frechet-Hoeffding bounds: if the chain rule holds in both directions (Bayes consistency), then

```
max(cred(A) + cred(B) - 1, 0) <= cred(A ∧ B) <= min(cred(A), cred(B))
```

This gives credence bounds on joints from marginals alone, without requiring a full joint specification.

### Asymptotic proof (from Part 2/3)

Show that credence converges to 1 under a specified sequence of updates (see `01-asymptotic-proofs.md`). This pattern produces certainty in the limit rather than in finite steps.

### Perturbation proof

Show a conclusion holds even under perturbation of premises:

```
If all cred(premise_i) >= 1 - e, then cred(conclusion) >= 1 - delta(e)
```

This is related to Adams' probability logic bounds (Part 2, consequence relations). It gives "noise-tolerant" derivations.

## What the labelled proof layer specifies

The Lean module `Cred.Sequent` supplies the first proof layer:

1. **Syntax**: formulas have no implication constructor
2. **Labels**: positive, certain, and threshold judgments
3. **Side judgments**: conditioning appears only as `c ∈ Cond(j,e)`
4. **Rules**: structural rules, imports from the verified consequence relations, and a chain-rule cut
5. **Soundness**: derivations respect the label semantics
6. **NoExFalso**: `A` and `~A` do not derive an unrelated positive conclusion

Completeness and cut elimination remain open.

## Comparison to classical

| Classical | Cred |
|-----------|------|
| Ex falso (from contradiction, anything) | Fails: conditioning at zero is unconstrained |
| Law of excluded middle (A or not-A is true) | Fails algebraically: c ⊔ ~c < 1 for c in (0,1) |
| Double negation elimination | Works: ~~c = c |
| Proof by contradiction | Requires care: deriving ~A from "assume A leads to contradiction" needs a consequence relation |
| Modus ponens | Available only after adding a residuated arrow; Cred conditioning itself stays external |
