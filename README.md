# Cred: A Foundation for Graded Mathematics

Cred is an algebra on **credences** (values in `[0,1]`) intended as a foundation for doing mathematics and reasoning when truth, evidence, and proofs are **graded** rather than purely Boolean. The core design choice is **primitive conditioning** via a chain rule equation/constraint, which blocks explosion from impossible evidence: when `cred(B)=0`, the equation imposes no constraint on `cred(A|B)` (no ex falso).

This repo contains:
- a Lean 4 library formalizing the Part 1 and Part 2 definitions and theorems (`lean/`)
- two publication papers aligned with the Lean source (`part1/paper.tex`, `part2/paper.tex`; built in CI)
- a roadmap toward new proof techniques/self-hosting (Part 3)

## Download Latest Papers (CI build)

- Part 1 (Core Algebra): [paper.pdf](https://github.com/krystophny/cred/releases/download/paper-latest/paper.pdf)
- Part 2 (From Algebra to Reasoning): [paper.pdf](https://github.com/krystophny/cred/releases/download/paper-part2-latest/paper.pdf)
- Per-run artifacts: [CI workflow runs](https://github.com/krystophny/cred/actions/workflows/ci.yml)

## Why This Exists

- **A foundation that tolerates impossibility without triviality:** classical material implication makes `⊥ → A` true for all `A`; Cred treats conditioning on `cred(B)=0` as underdetermined instead of forced.
- **Self-reference has fixed points, not contradictions:** self-negating equations like `L ≡ ¬L` stabilize at `cred(L)=0.5`.
- **Classical mathematics is a limiting case, not the starting point:** collapsing `[0,1]` down to `{0,1}` recovers familiar binary systems (and shows exactly what extra principles introduce ex falso).

## Current Milestone (Part 2)

Part 1 established the core algebra. Part 2 adds three layers—valuations, consequence relations, and update rules—and extends to first-order via graded predicates with inf/sup quantifiers. All results are machine-checked in Lean.

## Primitives (Part 1)

```
Values:       [0,1]
Negation:     ~c = 1 - c
Conjunction:  c₁ ⊗ c₂ = c₁·c₂
Disjunction:  c₁ ⊔ c₂ = ~(~c₁ ⊗ ~c₂)  (De Morgan dual; equals c₁ + c₂ - c₁·c₂)
Conditioning: cred(A|B) ⊗ cred(B) = cred(A ∧ B)  (primitive chain rule)
```

When `cred(B)=0`, the chain rule becomes `x·0=0`, satisfied by any `x`: conditioning is **unconstrained** at 0.

## Key Results (Lean)

Part 1 (core algebra):
- `Cred.Credence.conditioning_zero_any` — conditioning on 0 is unconstrained (no ex falso)
- `Cred.Credence.conditioning_unique` — uniqueness when evidence has positive credence
- `Cred.Credence.liar_fixed_point`, `Cred.Credence.neg_fixed_point_unique` — `0.5` fixed point and uniqueness
- `Cred.Credence.conj_disj_not_distrib` — `⊗` does not distribute over `⊔`

Part 2 (from algebra to reasoning):
- `Cred.CpValuation` — complement-preserving valuations with collapse composition
- `Cred.no_explosion_at_half` — explosion fails at credence `1/2`
- `Cred.bayesianUpdate_chain_rule` — Bayesian update preserves the chain rule
- `Cred.GradedPredicate.quantifier_duality_val` — `~(inf P) = sup (~P)` for graded quantifiers
- `Cred.GradedPredicate.russell_fixed_point` — Russell self-reference yields `1/2`

## Collapse Tower (orientation)

```
[0,1]  →  {0,½,1}  →  {0,1}  →  Classical (+material implication)
Cred      RM3-like    Relevant     (ex falso appears)
```

## Repo Layout

- `lean/` — Lean 4 formalization (authoritative for Part 1 and Part 2 definitions/theorems)
- `part1/` — paper + Part 1 notes (primitives and collapse connections)
- `part2/` — paper + Part 2 notes (valuations, consequence, update, graded predicates)
- `part3/` — roadmap: new proof techniques, undecidability, self-hosting

## Build

```bash
cd lean && lake build
cd part1 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
cd part2 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

## References

- Ramsey (1926), de Finetti (1937), Jaynes (2003) — credence foundations
- Rényi (1955), Popper (1959) — conditional probability as primitive
- Anderson & Belnap (1975) — relevant logic
