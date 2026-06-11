# CLAUDE.md

## Current Focus: Both papers publication-ready

Part 1: congruence classification of the product De Morgan triplet (6 sections + conclusion + 2 appendices, 12 pages).
Part 2: self-contained paper — chain-rule conditioning as a bridge between probability and many-valued logic (8 sections + 2 appendices, 24 pages).
All Lean proofs fully verified (3758 lines across 13 modules, zero sorry). Both papers build clean.

## Build (match CI)

```bash
cd lean && lake build              # Lean formalization
cd part1 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex   # Paper (preferred)
# fallback:
# cd part1 && pdflatex paper.tex && pdflatex paper.tex
```

Toolchain: Lean `v4.16.0` + mathlib `v4.16.0`. Correctness = `lake build` succeeds and theorems type-check.

## Primitives

```
[0,1]   credence values
0       impossibility
1       certainty
~c      negation (1 - c)
c₁⊗c₂   conjunction (product)
c₁⊔c₂   disjunction (De Morgan dual)
(A|B)   conditioning (primitive; chain rule)
```

**Chain rule (primitive conditioning):** `cred(A|B) ⊗ cred(B) = cred(A ∧ B)`

When `cred(B) = 0`: the equation imposes no constraint on `cred(A|B)` (any value works). There is intentionally **no ex falso** / explosion from impossible evidence.

Keep the separation clear: `⊗`/`⊔` are the core algebraic operations (product / De Morgan dual). Dependence is handled by supplying an explicit joint credence in `Cred.Credence.Conditioning` rather than treating `⊗` as a general rule for `cred(A ∧ B)`.

## Repo Map

- `lean/Cred/Core/Value.lean` — credence values: negation, product conjunction, disjunction, order, fixed points, spread, equilibria (426 lines).
- `lean/Cred/Core/Consequence.lean` — K3/LP designation, graded consequence, Formula, eval, structural rules, no-explosion theorems (316 lines).
- `lean/Cred/Cond/Admissible.lean` — chain-rule conditioning, admissible sets (Cond), Fréchet bounds, conditioning tables, path dependence (427 lines).
- `lean/Cred/Cond/Copula.lean` — Bayes consistency on [0,1], min-copula uniqueness, world partitioning (403 lines).
- `lean/Cred/Collapse/ThreeVal.lean` — three-valued credences, RM3/Gödel/product-residuated implications (227 lines).
- `lean/Cred/Collapse/Hom.lean` — collapse homomorphism, no-Gödel/no-Łukasiewicz collapse, Boolean subalgebra (313 lines).
- `lean/Cred/Congruence/Unit.lean` — UnitCongruence classification, Kleene witness, three-element quotient uniqueness (297 lines).
- `lean/Cred/Congruence/Real.lean` — RealCongruence, scaling trick, no non-trivial finite quotient (229 lines).
- `lean/Cred/Bridge/LPK3.lean` — collapse-eval commutativity, LP/K3 bridge theorems (207 lines).
- `lean/Cred/Bridge/CondBridge.lean` — conditional bridge: impossibility, boundary, update bridge, zero-evidence triple (389 lines).
- `lean/Cred/Valuation.lean` — valuations (CpValuation, IndepValuation, JointValuation) (176 lines).
- `lean/Cred/Update.lean` — Bayesian and Jeffrey conditionalization (138 lines).
- `lean/Cred/Predicate.lean` — graded predicates, quantifiers, Russell fixed point (210 lines).
- `part1/paper.tex` — congruence classification (6 sections + conclusion + 2 appendices, 12 pages).
- `part2/paper.tex` — bridge paper (8 sections + 2 appendices, 24 pages; self-contained).
- `part3/` — future work: graded proofs, self-hosting, undecidability.

## Key Results to Keep Green (Lean)

Core:
- `Cred.Credence.conditioning_zero_any` (conditioning on 0 is unconstrained)
- `Cred.Credence.conditioning_unique` (uniqueness when evidence has positive credence)
- `Cred.Credence.liar_fixed_point`, `Cred.Credence.neg_fixed_point_unique` (0.5 fixed point and uniqueness)
- `Cred.Credence.conj_disj_not_distrib` (⊗ does not distribute over ⊔)

Admissible-set conditioning (Cond/Admissible.lean, Bridge/CondBridge.lean):
- `Cred.Credence.Cond` (admissible set {c | c ⊗ e = j} as named primitive)
- `cond_singleton_of_pos`, `cond_zero_zero_univ`, `cond_nonempty_iff` (trichotomy: singleton / full interval / empty)
- `mem_cond_iff` (membership = Conditioning witness)
- `zero_evidence_duality_cond`, `cond_interior_range` (CondBridge restatements through Cond)

Collapse / congruence:
- `Cred.ThreeVal.rm3_ex_falso` (RM3 implication has explosion row)
- `Cred.ThreeVal.cred_no_ex_falso` (Cred blocks ex falso via unconstrained conditioning)
- `three_element_quotient_unique`, `zero_equiv_forces_trivial`, `no_boolean_neg_retraction`
- `Cred.UnitCongruence.singleton_zero`, `singleton_one` (boundary singletons under [0,1]-mult)
- `Cred.RealCongruence.no_nontrivial_finite_quotient` (scaling trick, no finite quotient under R-mult)
- `Cred.kleeneCongruence` (Kleene partition as verified UnitCongruence)

Bridge (from Bridge/LPK3.lean and Core/Consequence.lean):
- `lp_formula_bridge`, `k3_formula_bridge` (LP = positivity, K3 = certainty consequence)
- `k3_no_tautology`, `lp_no_explosion`, `graded_no_explosion`

Conditional bridge (from Bridge/CondBridge.lean):
- `no_truthfunctional_cond_bridge` (impossibility: no truth-functional conditional bridge)
- `cond_bridge_boundary` (bridge holds at boundaries)
- `cond_bridge_fails_interior` (bridge fails for interior pairs)
- `update_bridge` (Bayesian update inherits the bridge)
- `zero_evidence_duality` (zero-evidence triple)

Predicates (from Predicate.lean):
- `quantifier_duality_val`, `russell_fixed_point`, `crisp_inf_zero_iff`

## Philosophy

**Inference constrains:** evidence narrows possibilities from prior uncertainty; impossible evidence (credence 0) provides no constraint.

**Conditional first:** conditioning is primitive (chain rule), not division; this is the key design choice that avoids explosion at 0.
