# Open Questions (Part 3 Roadmap)

Part 3 is where we stop re-stating Parts 1--2 and instead decide what *extra*
structure to add, what theorems to target, and how to position Cred relative to
existing traditions (mathematical fuzzy logic, coherence/conditional events,
imprecise probability, and fixed-point semantics for truth).

For a literature map and synthesis statement, see `paper-sketch.tex`.

## Baselines (things to not reinvent)

1. **Mathematical fuzzy logic / product logic.** If we fix the joint to the
   Fréchet upper bound `min(a,b)`, Cred's conditioning matches the
   product-residuated (Goguen) implication for positive evidence. This puts the
   logic-style view directly adjacent to product logic and BL/MTL families
   (Hájek, Klement--Mesiar--Pap; Handbook; residuated lattices).

2. **Conditional probability as primitive + conditional events.** Rényi/Popper
   conditioning, de Finetti's void conditional, Calabrese Boolean fractions, and
   coherence-based conditional random quantities already treat the antecedent-false
   case as non-classical (void/underdetermined) rather than vacuously true.

3. **Null-event conditioning + imprecise probability.** Measure-theoretic
   disintegration gives conditionals determined only up to almost-sure equivalence;
   imprecise probability often returns sets/intervals of admissible conditionals
   at the boundary rather than a single value.

4. **Fixed-point semantics for truth.** Kripke fixed points and revision theory
   already provide mature frameworks for self-reference. Cred's `c = 1-c` fixed
   point is a clean algebraic base case, not a replacement for that literature.

## Proof theory (graded consequence vs graded provability)

1. **Pick a proof target.** Are we aiming for (a) a threshold semantics on
   `[0,1]` (Part 2 style), (b) a designated-values system after collapse (K3/LP),
   or (c) Pavelka-style graded provability? These lead to different calculi and
   different completeness statements.

2. **Soundness/completeness.** For whichever target is chosen, can we state a
   soundness theorem against the Part 2 semantics, and a completeness theorem
   that does not silently smuggle in ex falso via the `0 -> b = 1` convention?

3. **Cut elimination / admissibility.** If a sequent or hypersequent calculus is
   used, do we get a clean normalization property (cut elimination), and what
   meta-theorems survive in the graded setting?

## Zero evidence and dynamics

4. **Update at zero evidence.** What is the Cred analogue of disintegration or
   regular extension? The Cred stance is underdetermination at `cred(B)=0`; Part 3
   should decide whether to (a) keep it set-valued/interval-valued, (b) add a
   selection principle (a coherence criterion), or (c) supply additional structure
   (measure, Markov-kernel semantics, probabilistic program semantics).

5. **Coherence conditions for updates.** Dutch book arguments constrain Bayesian
   updating in probability. What are the analogous coherence constraints for Cred
   update rules (Bayesian/Jeffrey-style for positive evidence plus a boundary rule)?

6. **Asymptotic proof.** When does a specified update process force `cred_n(P) -> 1`?
   Which convergence rates are provable from the update axioms alone?

## Self-reference

7. **Beyond the liar.** Which operator families `phi : [0,1] -> [0,1]` are
   natural in Cred-style semantics and yield (i) unique interior fixed points,
   (ii) multiple fixed points, or (iii) no fixed points?

8. **Mutual reference systems.** For finite systems of mutually referring
   statements, characterize the solution sets and stability under iteration.

9. **Interface to truth semantics.** Make explicit which self-reference results
   are purely algebraic (Part 1 style) and which require proof-theoretic or
   semantic machinery (Kripke/revision).

## Graded foundations

10. **Graded extensionality and comprehension.** If sets are predicates into
    `[0,1]`, what are the right analogues of extensionality and comprehension?
    Use many-valued set theory as a constraint on what is plausible.

11. **Crisp subtheories.** Identify and formalize the crisp fragments (where all
    credences are `0/1`) and prove they recover the intended classical theorems.

## Connections and implementation

12. **Relationship to relevant logic.** With `min` as the joint, the induced
    arrow matches product residuation for positive evidence, while the collapse
    maps the connective algebra to the Kleene lattice. What is the cleanest way
    to express the relationship to RM3/R/E without conflating arrows, collapses,
    and consequence relations?

13. **Probabilistic programming semantics.** Can the chain rule be made the core
    equational law of an `observe`/conditioning primitive while preserving the
    evidence-zero underdetermination?

14. **Tooling.** Once a proof target is fixed, a Cred-aware assistant becomes an
    engineering task rather than a research question. Until then, treat it as
    downstream.
