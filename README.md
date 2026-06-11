# Cred: Admissible Conditioning over Graded Credences

Cred is two modules plus an interface, machine-checked in Lean 4.

- **Axis A: admissible conditional semantics (non-explosion).** Conditioning is an admissibility relation, not a connective. The chain rule `cred(A|B) ⊗ cred(B) = cred(A ∧ B)` defines the admissible set `Cond(j,e) = {c | c ⊗ e = j}` for joint `j` and evidence `e`. Positive evidence yields a singleton (Bayes); zero evidence with zero joint yields the full interval `[0,1]`. No inference rule is weakened: explosion never starts, because impossible evidence forces no value.
- **Axis B: graded credence semantics.** The value space `[0,1]` with the product De Morgan triplet (product conjunction, probabilistic-sum disjunction, standard complement), its Kleene quotient `{0, ½, 1}`, and the LP/K3 consequence bridges.
- **The interface.** The axes combine above the propositional layer and stay independent: `no_truthfunctional_cond_bridge` proves that no truth-functional conditional on the collapsed values reproduces admissible conditioning. The axes do not reduce to each other, even after collapse.

This repo contains:
- a Lean 4 formalization (3581 lines across 7 modules, zero `sorry`; `lean/`)
- two papers aligned with the Lean source (`part1/paper.tex`, `part2/paper.tex`; built in CI)
- a foundations program: fixed points, graded comprehension, crisp fragment (`part3/`)

## Download Latest Papers (CI build)

- Part 1 (Congruence Classification): [paper.pdf](https://github.com/krystophny/cred/releases/download/paper-latest/paper.pdf)
- Part 2 (Bridge between Probability and Many-Valued Logic): [paper.pdf](https://github.com/krystophny/cred/releases/download/paper-part2-latest/paper.pdf)
- Per-run artifacts: [CI workflow runs](https://github.com/krystophny/cred/actions/workflows/ci.yml)

## Architecture

```
Axis B   value semantics    [0,1], Kleene quotient; later intervals, credal sets
Axis A1  consequence        positivity, certainty, threshold-t
Axis A2  conditioning       admissible sets Cond(j,e)
Foundations                 fixed points, graded comprehension, crisp fragment
Proof layer                 labelled sequents, external conditioning judgment
```

No layer contains an internal object-language conditional. Conditionals enter only as the external judgment `c ∈ Cond(j,e)`; entailment and conditioning stay metalinguistic relations. The same choice blocks Curry-style internalization.

In the foundations layer, self-reference lands on solution sets instead of contradictions: the liar equation `L ≡ ¬L` stabilizes at `cred(L) = 0.5`. Fixed points are formalized (`liar_fixed_point`, `russell_fixed_point`); graded comprehension, the crisp fragment, and the labelled sequent calculus are in progress.

## Primitives

```
Values:       [0,1]
Negation:     ~c = 1 - c
Conjunction:  c₁ ⊗ c₂ = c₁·c₂        (product t-norm)
Disjunction:  c₁ ⊔ c₂ = ~(~c₁ ⊗ ~c₂)  (De Morgan dual; equals c₁ + c₂ - c₁·c₂)
Conditioning: cred(A|B) ⊗ cred(B) = cred(A ∧ B)  (chain rule; joint via min copula)
```

## Key Results (Lean)

Axis A, admissible conditioning (Part 1 paper):
- `conditioning_zero_any`: conditioning on 0 is unconstrained (no ex falso)
- `conditioning_unique`: uniqueness when evidence has positive credence

Axis B, graded values (Part 1 paper):
- `liar_fixed_point`, `neg_fixed_point_unique`: `0.5` fixed point and uniqueness
- `three_element_quotient_unique`: any 3-element quotient preserving negation and conjunction is the Kleene lattice
- `UnitCongruence.singleton_zero/one`: boundary classes are singletons under `[0,1]`-multiplication
- `RealCongruence.no_nontrivial_finite_quotient`: no finite quotient under R-multiplication

Interface (Part 2 paper):
- `lp_formula_bridge`: LP consequence = positivity consequence on `[0,1]`
- `k3_formula_bridge`: K3 consequence = certainty consequence on `[0,1]`
- `no_truthfunctional_cond_bridge`: the independence theorem; no truth-functional conditional bridge exists
- `cond_bridge_boundary`: the conditional bridge holds at boundaries
- `update_bridge`: Bayesian update inherits the bridge under boundary conditions
- `zero_evidence_duality`: zero-evidence triple (underdetermination, LP explosion failure, bridge failure)

## Collapse

```
[0,1]  →  {0,½,1}      →  {0,1}
Cred      Kleene lattice    Classical
          (K3/LP/RM3)
```

The collapse is a surjective homomorphism. It faithfully preserves propositional consequence (the bridge) but cannot preserve conditioning (Lewis-type impossibility). Ex falso appears whenever conditioning is defined via residuation or material implication, already at the Kleene level (Gödel: `0 → p = 1`). Chain-rule conditioning avoids it at every level by leaving the conditional unconstrained at evidence zero.

## Claim Discipline

Each ingredient has its own literature: paraconsistency (Priest 1979; Carnielli and Coniglio 2016), graded truth (Zadeh 1965; Hájek 1998), primitive conditional probability (Rényi 1955; Popper 1959), defective conditionals (de Finetti 1936; Égré, Rossi and Sprenger 2021), imprecise probability (Walley 1991). Cred claims the combination and its formalization: zero-evidence underdetermination as a logical principle, the LP/K3 collapse bridges, a no-go theorem against truth-functional reconstruction of conditioning, all machine-checked.

## Repo Layout

- `lean/`: Lean 4 + Mathlib formalization (7 modules, 3581 lines, zero `sorry`)
- `part1/`: Part 1 paper: congruence classification of the product De Morgan triplet (axis B)
- `part2/`: Part 2 paper: chain-rule conditioning as a bridge between probability and many-valued logic (the interface; self-contained)
- `part3/`: foundations program: fixed points, graded comprehension, crisp fragment

## Build

```bash
cd lean && lake build
cd part1 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
cd part2 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

Toolchain: Lean 4.16.0 + Mathlib 4.16.0.

## References

- Kleene (1952): three-valued logic and the Kleene lattice
- Hájek (1998): Product Logic and the product t-norm
- Rényi (1955), Popper (1959), de Finetti (1936): primitive conditioning
- Égré, Rossi, Sprenger (2021): de Finettian logics of indicative conditionals
- Priest (1979), Carnielli and Coniglio (2016): paraconsistency
- Walley (1991): imprecise probability
- Cox (1961), Jaynes (2003): probability as extended logic
- Klement, Mesiar, Pap (2000): triangular norms and De Morgan triplets

## Acknowledgements

Anthropic's Claude (Opus 4.5 and 4.6) was used as an assistant for both the Lean formalization and the manuscript preparation.
