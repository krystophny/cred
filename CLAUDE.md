# CLAUDE.md

## Current Focus: Part 1 (publication-ready), Part 2 (companion)

Part 1 focused on congruence classification (sections 1-7). Part 2 has applied material (valuations, update, consequence, predicates).
All Lean proofs fully verified (zero sorry). Both papers build clean.

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
- `lean/Cred/Congruence.lean` — congruence classification (all four parts fully verified).
- `part1/paper.tex` — congruence classification (7 sections + 2 appendices, 12 pages).
- `part2/paper.tex` — valuations, update, consequence, predicates (4 sections + 1 appendix, 6 pages).
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
- `Cred.CredCongruence.singleton_zero`, `singleton_one` (boundary singletons)
- `Cred.CredCongruence.no_four_or_more_classes` (scaling trick, fully verified)

Consequence (from Consequence.lean):
- `k3_no_tautology`, `lp_no_explosion`, `graded_no_explosion`

Predicates (from Predicate.lean):
- `quantifier_duality_val`, `russell_fixed_point`, `crisp_inf_zero_iff`

## Philosophy

**Inference constrains:** evidence narrows possibilities from prior uncertainty; impossible evidence (credence 0) provides no constraint.

**Conditional first:** conditioning is primitive (chain rule), not division; this is the key design choice that avoids explosion at 0.
