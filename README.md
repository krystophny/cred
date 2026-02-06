# Cred: Chain-Rule Conditioning as a Bridge between Probability and Many-Valued Logic

Cred is an algebra on **credences** (values in `[0,1]`) built from the **product De Morgan triplet** (product conjunction, probabilistic-sum disjunction, standard complement) with **chain-rule conditioning** as the primitive conditional. When `cred(B)=0`, the chain rule `cred(A|B) ⊗ cred(B) = cred(A ∧ B)` becomes `x·0=0`, satisfied by any `x`: conditioning is **unconstrained** at zero (no ex falso).

This repo contains:
- a Lean 4 formalization (3581 lines across 7 modules, zero `sorry`; `lean/`)
- two papers aligned with the Lean source (`part1/paper.tex`, `part2/paper.tex`; built in CI)
- a roadmap toward graded proofs and self-hosting (Part 3)

## Download Latest Papers (CI build)

- Part 1 (Congruence Classification): [paper.pdf](https://github.com/krystophny/cred/releases/download/paper-latest/paper.pdf)
- Part 2 (Bridge between Probability and Many-Valued Logic): [paper.pdf](https://github.com/krystophny/cred/releases/download/paper-part2-latest/paper.pdf)
- Per-run artifacts: [CI workflow runs](https://github.com/krystophny/cred/actions/workflows/ci.yml)

## Why This Exists

- **Impossible evidence provides no constraint:** classical material implication makes `⊥ → A` true for all `A`; chain-rule conditioning leaves `cred(A|0)` unconstrained.
- **Self-reference has fixed points, not contradictions:** self-negating equations like `L ≡ ¬L` stabilize at `cred(L)=0.5`.
- **Many-valued logic is a quotient, not a separate system:** the product De Morgan triplet on `[0,1]` collapses to the Kleene lattice `{0, ½, 1}` via a unique three-element quotient, recovering K3/LP/RM3.

## Primitives

```
Values:       [0,1]
Negation:     ~c = 1 - c
Conjunction:  c₁ ⊗ c₂ = c₁·c₂        (product t-norm)
Disjunction:  c₁ ⊔ c₂ = ~(~c₁ ⊗ ~c₂)  (De Morgan dual; equals c₁ + c₂ - c₁·c₂)
Conditioning: cred(A|B) ⊗ cred(B) = cred(A ∧ B)  (chain rule; joint via min copula)
```

## Key Results (Lean)

Part 1 — core algebra and congruence classification:
- `conditioning_zero_any` — conditioning on 0 is unconstrained (no ex falso)
- `conditioning_unique` — uniqueness when evidence has positive credence
- `liar_fixed_point`, `neg_fixed_point_unique` — `0.5` fixed point and uniqueness
- `three_element_quotient_unique` — any 3-element quotient preserving negation and conjunction is the Kleene lattice
- `UnitCongruence.singleton_zero/one` — boundary classes are singletons under `[0,1]`-multiplication
- `RealCongruence.no_nontrivial_finite_quotient` — no finite quotient under R-multiplication

Part 2 — bridge between probability and many-valued logic:
- `lp_formula_bridge` — LP consequence = positivity consequence on `[0,1]`
- `k3_formula_bridge` — K3 consequence = certainty consequence on `[0,1]`
- `no_truthfunctional_cond_bridge` — no truth-functional conditional bridge exists
- `cond_bridge_boundary` — the conditional bridge holds at boundaries
- `update_bridge` — Bayesian update inherits the bridge under boundary conditions
- `zero_evidence_duality` — zero-evidence triple: underdetermination + paraconsistency + bridge failure

## Collapse

```
[0,1]  →  {0,½,1}      →  {0,1}
Cred      Kleene lattice    Classical (ex falso appears)
          (K3/LP/RM3)
```

The collapse is a surjective homomorphism. It faithfully preserves propositional consequence (the bridge) but cannot preserve conditioning (Lewis-type impossibility).

## Repo Layout

- `lean/` — Lean 4 + Mathlib formalization (7 modules, 3581 lines, zero `sorry`)
- `part1/` — Part 1 paper: congruence classification of the product De Morgan triplet
- `part2/` — Part 2 paper: chain-rule conditioning as a bridge (self-contained)
- `part3/` — future work: graded proofs, self-hosting, undecidability

## Build

```bash
cd lean && lake build
cd part1 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
cd part2 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

Toolchain: Lean 4.16.0 + Mathlib 4.16.0.

## References

- Kleene (1952) — three-valued logic and the Kleene lattice
- Hajek (1998) — Product Logic and the product t-norm
- Renyi (1955), Popper (1959), de Finetti (1936) — primitive conditioning
- Cox (1961), Jaynes (2003) — probability as extended logic
- Klement, Mesiar, Pap (2000) — triangular norms and De Morgan triplets
