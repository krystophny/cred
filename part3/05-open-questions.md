# Open Questions

Part 3 is where we stop re-stating Parts 1--2 and instead decide what *extra*
structure to add, what theorems to target, and how to position Cred relative to
existing traditions (mathematical fuzzy logic, coherence/conditional events,
imprecise probability, and fixed-point semantics for truth).

For the current synthesis statement, see `paper.tex`.

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

1. **Proof target.** The implemented calculus in `lean/Cred/Sequent.lean`
   tracks positive, certain, and threshold labels. Conditioning remains an
   external side judgment. Pavelka-style graded provability is still a separate
   target, with a different completeness statement.

2. **Completeness.** Soundness is formalized for labelled derivations. A
   completeness theorem remains open. It must not smuggle in ex falso through
   the `0 -> b = 1` convention.

3. **Cut elimination / admissibility.** The calculus has a sound cut rule. A
   normalization theorem remains open, including the exact meta-theorems that
   survive in the graded setting.

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
    Use many-valued set theory as a constraint on what is plausible. The first
    object-language module is `lean/Cred/Foundation/Language.lean`; equality,
    quantifiers, and binder-aware substitution are explicit, while
    conditionality remains external.
    `lean/Cred/Foundation/Semantics.lean` interprets formulas into credences
    using explicit equality and quantifier operations. Crispness and
    extensionality remain separate laws.
    `lean/Cred/Foundation/Laws.lean` now names the first law interfaces:
    crisp equality and quantifier bounds.

11. **Crisp subtheories.** Identify and formalize the crisp fragments (where all
    credences are `0/1`) and prove they recover the intended classical theorems.

## Connections and implementation

12. **Relationship to relevant logic.** With the min-copula joint, the induced
    positive-evidence arrow matches product residuation, while the collapse maps
    the connective algebra to the Kleene lattice. The comparison must keep
    arrows, collapses, and consequence relations separate.

13. **Probabilistic programming semantics.** Can the chain rule be made the core
    equational law of an `observe`/conditioning primitive while preserving the
    evidence-zero underdetermination?

14. **Kernel and tooling.** `lean/Cred/Kernel.lean` now defines type-level proof
    certificates for labelled derivations. The next engineering target is a
    small serializable checker whose accepted certificates erase to
    `Kernel.Proof`. Tactics, automation, and editor support come after that
    kernel boundary is small and stable.
