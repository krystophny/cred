# Open Questions for Part 2

## Consequence relations

1. **Which consequence relations are compatible with unconstrained conditioning at zero?**
   Part 1 establishes that conditioning on evidence with credence zero is unconstrained. A compatible consequence relation must not have explosion (from A and ~A, derive anything). K3, LP, and RM3 are compatible; classical consequence is not. Are there others?

2. **Is there a natural consequence relation for Cred on [0,1]?**
   The collapse gives three-valued consequence relations via K3/LP/RM3. Is there a direct consequence relation on [0,1] that does not factor through the collapse?

3. **Adams-type bounds without additivity.**
   Adams' probability logic uses sigma-additivity to propagate uncertainty bounds through inference. Can analogous bounds be proven for Cred valuations that lack additivity? What structure must be added?

## Update rules

4. **Update at zero evidence.**
   Bayesian and Jeffrey conditionalization both require positive evidence. What happens in Cred when you learn something you previously assigned credence zero? Probability resolves this via disintegration; what is the Cred analogue?

5. **Constraint propagation as an update mechanism.**
   Rather than committing to a single posterior, could a Cred update propagate chain-rule constraints and report a *set* of compatible posteriors? This connects to imprecise probability (sets of probability measures).

6. **Coherence conditions on Cred update rules.**
   Dutch book arguments constrain Bayesian updating in probability. What are the analogous coherence conditions for Cred? The chain rule is necessary; is it sufficient?

## Predicates and quantifiers

7. **First-order Cred.**
   Part 1 is propositional. Extending to first order requires quantifiers (inf/sup), predicates, and potentially variable-binding. What axioms are needed beyond Part 1 to get a well-behaved first-order system?

8. **Graded set theory.**
   Unrestricted comprehension gives fixed points instead of paradoxes. Can a useful fragment of set theory be built on Cred predicates? What is the analogue of the axiom of extensionality for graded predicates?

## Connections

9. **Imprecise probability.**
   Cred's unconstrained conditioning at zero resembles the indeterminate conditionals of imprecise probability (sets of probability measures). How far does this analogy go?

10. **Probabilistic programming.**
    Probabilistic programming languages (Stan, Pyro, etc.) use conditioning as a primitive operation. How does Cred's chain rule relate to the observe/condition constructs in these languages?

11. **Game semantics.**
    Fermuller (2014) showed that straightforward evaluation games lead to Kleene logic. Part 1 cites this result. Can Cred valuations be characterized game-semantically?
