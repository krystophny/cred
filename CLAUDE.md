# CLAUDE.md

## Current Focus: Part 1 (next milestone)

Ship a publication-quality `part1/paper.tex` that matches the machine-checked core algebra in `lean/Cred/Basic.lean`.

Avoid scope creep into `part2/` (graded mathematics) and `part3/` (self-hosting / undecidability techniques) unless a Part 1 result needs a small cross-reference.

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

## Repo Map (Part 1)

- `lean/Cred/Basic.lean` — authoritative definitions + full proofs (core algebra, conditioning, fixed points, non-distributivity, and 3-valued collapse/RM3 comparison).
- `part1/paper.tex` — publication paper (keep its named claims aligned with Lean; CI produces a PDF artifact).
- `part1/*.md` — supporting notes for exposition/collapse tower (non-authoritative, but keep consistent with the paper).

## Key Results to Keep Green (Lean)

Core:
- `Cred.Credence.conditioning_zero_any` (conditioning on 0 is unconstrained)
- `Cred.Credence.conditioning_unique` (uniqueness when evidence has positive credence)
- `Cred.Credence.liar_fixed_point`, `Cred.Credence.neg_fixed_point_unique` (0.5 fixed point and uniqueness)
- `Cred.Credence.conj_disj_not_distrib` (⊗ does not distribute over ⊔)

Collapse / comparisons (used in Part 1 exposition):
- `Cred.ThreeVal.rm3_ex_falso` (RM3 implication has explosion row)
- `Cred.ThreeVal.cred_no_ex_falso` (Cred blocks ex falso via unconstrained conditioning)

## Philosophy

**Inference constrains:** evidence narrows possibilities from prior uncertainty; impossible evidence (credence 0) provides no constraint.

**Conditional first:** conditioning is primitive (chain rule), not division; this is the key design choice that avoids explosion at 0.
