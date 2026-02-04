# Open Questions

## Already settled by Parts 1-2

These questions from earlier drafts are now answered:

- **"Does Cred have a model?"** — Yes. [0,1] with the product, complement, and chain rule IS the model. Part 1 defines Cred as this concrete algebra and Lean-checks it.
- **"Is Cred consistent?"** — Cred is an algebra, not a formal theory. The algebra trivially has a model ([0,1] itself). Consistency becomes a question only when Cred is extended to a formal theory with axioms and a proof system.
- **"Does Cred solve the liar paradox?"** — The liar sentence has credence 1/2 (Part 1, Lean: `liar_fixed_point`). Whether this counts as "solving" the paradox is philosophical, not mathematical.
- **"What about Godel?"** — Godel sentences are not self-negating; they have definite truth values in standard models. Cred does not dissolve incompleteness. See `03-undecidability.md`.

## Proof theory

1. **Sequent calculus for Cred.** What is a sound and complete proof system for Cred? What are the sequent rules? Does cut elimination hold?

2. **Decidability.** Is validity (or satisfiability) in a Cred-based logic decidable? What complexity class?

3. **Proof-theoretic strength.** How does a Cred proof system compare in strength to classical logic, K3, LP, or product logic?

## Consequence relations

4. **Compatibility with unconstrained conditioning.** Which consequence relations (beyond K3, LP, RM3) are compatible with the principle that impossible evidence provides no constraint? Part 2 poses this question; it remains open.

5. **Adams-type bounds without additivity.** Adams' probability logic uses sigma-additivity to propagate uncertainty. Can analogous bounds be proven for Cred valuations without additivity?

6. **Natural consequence relation on [0,1].** Is there a consequence relation directly on [0,1] credences (not factoring through the three-valued collapse) that is sound with respect to the algebra?

## Update rules and dynamics

7. **Coherence conditions for Cred updates.** Dutch book arguments constrain Bayesian updating in probability. What are the analogous coherence conditions for Cred update rules?

8. **Update at zero evidence.** What should happen when you learn something you previously assigned credence zero? Probability uses disintegration. What is the Cred analogue?

## Self-reference and fixed points

9. **Fixed points beyond negation.** Which continuous self-referential operators f : [0,1] -> [0,1] yield unique interior fixed points? Negation does (c = 1/2). Product and De Morgan dual do not (boundary only).

10. **Mutual reference.** For systems of n mutually referencing statements, what determines the dimension and structure of the solution set?

11. **Lawvere's fixed point theorem.** Does Lawvere's categorical generalization of diagonal arguments apply to Cred's self-reference?

## Connections to other systems

12. **Relationship to relevant logic.** Part 1 shares the product De Morgan triplet with product fuzzy logic and collapses to the Kleene lattice (underlying K3/LP/RM3). What is the precise relationship to the relevant logics R, E, RM? Is a Cred-based system a known relevant logic or a new one?

13. **Paraconsistent set theory.** Brady and Weber developed mathematics on paraconsistent logic. How does Cred's graded predicate approach (fixed points instead of contradictions) compare?

14. **Probabilistic programming.** Probabilistic programming languages use conditioning as a primitive (observe/condition). How does Cred's chain rule relate to these constructs?

15. **Higher-order quantification.** Part 2 defines first-order quantifiers as inf/sup. Second-order: inf/sup over predicates. Does this require restricting to measurable predicates, or does the algebraic approach avoid measure-theoretic issues?

## Implementation

16. **Cred proof assistant.** Can a proof assistant be built that tracks credences through derivations? What would its type theory look like?

17. **Computational complexity of credence tracking.** In a Cred-based proof system, what is the cost of tracking credences through a derivation? Is it polynomial in proof length?

## Research priorities

From most concrete to most speculative:

1. Sequent calculus / proof system (builds directly on Parts 1-2)
2. Relationship to relevant logic (comparison with known systems)
3. Adams-type bounds without additivity (extends Part 2 consequence relations)
4. Coherence conditions for updates (extends Part 2 update rules)
5. Cred proof assistant (implementation, requires answers to 1-4)
