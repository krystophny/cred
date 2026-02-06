# CLAUDE.md

## Current Focus: Both papers publication-ready

Part 1: congruence classification of the product De Morgan triplet (6 sections + conclusion + 2 appendices, 12 pages).
Part 2: self-contained paper — chain-rule conditioning as a bridge between probability and many-valued logic (8 sections + 2 appendices, 24 pages).
All Lean proofs fully verified (3581 lines across 7 modules, zero sorry). Both papers build clean.

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

- `lean/Cred/Basic.lean` — core algebra, conditioning, fixed points, collapse, congruence building blocks, impossibility results, Bayes consistency, path dependence.
- `lean/Cred/Valuation.lean` — valuations (CpValuation, IndepValuation, JointValuation).
- `lean/Cred/Consequence.lean` — K3/LP/graded consequence, no-explosion theorems.
- `lean/Cred/Update.lean` — Bayesian and Jeffrey conditionalization.
- `lean/Cred/Predicate.lean` — graded predicates, quantifiers, Russell fixed point.
- `lean/Cred/Congruence.lean` — two-level congruence classification (UnitCongruence, RealCongruence, Kleene witness).
- `lean/Cred/CondBridge.lean` — conditional bridge: impossibility, boundary, update bridge, zero-evidence triple (353 lines).
- `part1/paper.tex` — congruence classification (6 sections + conclusion + 2 appendices, 12 pages).
- `part2/paper.tex` — bridge paper (8 sections + 2 appendices, 24 pages; self-contained).
- `part3/` — future work: graded proofs, self-hosting, undecidability.

## Key Results to Keep Green (Lean)

Core:
- `Cred.Credence.conditioning_zero_any` (conditioning on 0 is unconstrained)
- `Cred.Credence.conditioning_unique` (uniqueness when evidence has positive credence)
- `Cred.Credence.liar_fixed_point`, `Cred.Credence.neg_fixed_point_unique` (0.5 fixed point and uniqueness)
- `Cred.Credence.conj_disj_not_distrib` (⊗ does not distribute over ⊔)

Collapse / congruence:
- `Cred.ThreeVal.rm3_ex_falso` (RM3 implication has explosion row)
- `Cred.ThreeVal.cred_no_ex_falso` (Cred blocks ex falso via unconstrained conditioning)
- `three_element_quotient_unique`, `zero_equiv_forces_trivial`, `no_boolean_neg_retraction`
- `Cred.UnitCongruence.singleton_zero`, `singleton_one` (boundary singletons under [0,1]-mult)
- `Cred.RealCongruence.no_nontrivial_finite_quotient` (scaling trick, no finite quotient under R-mult)
- `Cred.kleeneCongruence` (Kleene partition as verified UnitCongruence)

Bridge (from Consequence.lean):
- `lp_formula_bridge`, `k3_formula_bridge` (LP = positivity, K3 = certainty consequence)
- `k3_no_tautology`, `lp_no_explosion`, `graded_no_explosion`

Conditional bridge (from CondBridge.lean):
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
