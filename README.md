# Cred: A Foundation for Graded Mathematics

Cred is an algebra on **credences** (values in `[0,1]`) intended as a foundation for doing mathematics and reasoning when truth, evidence, and proofs are **graded** rather than purely Boolean. The core design choice is **primitive conditioning** via a chain rule equation/constraint, which blocks explosion from impossible evidence: when `cred(B)=0`, the equation imposes no constraint on `cred(A|B)` (no ex falso).

This repo contains:
- a Lean 4 library formalizing the Part 1 primitives and theorems (`lean/`)
- a publication paper aligned with the Lean source (`part1/paper.tex`; built in CI)
- a roadmap toward graded mathematics (Part 2) and new proof techniques/self-hosting (Part 3)

## Download Latest Paper (CI build)

- Latest PDF: [paper.pdf](releases/download/paper-latest/paper.pdf)
- Per-run artifacts: [CI workflow runs](actions/workflows/ci.yml) (open the latest successful run and download `cred-paper-pdf`)

## Why This Exists

- **A foundation that tolerates impossibility without triviality:** classical material implication makes `⊥ → A` true for all `A`; Cred treats conditioning on `cred(B)=0` as underdetermined instead of forced.
- **Self-reference has fixed points, not contradictions:** self-negating equations like `L ≡ ¬L` stabilize at `cred(L)=0.5`.
- **Classical mathematics is a limiting case, not the starting point:** collapsing `[0,1]` down to `{0,1}` recovers familiar binary systems (and shows exactly what extra principles introduce ex falso).

## Current Milestone (Part 1)

Establish the core Cred algebra with full Lean proofs and a paper that makes the motivation and consequences obvious on first read.

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

- `Cred.Credence.conditioning_zero_any` — conditioning on 0 is unconstrained (no ex falso)
- `Cred.Credence.conditioning_unique` — uniqueness when evidence has positive credence
- `Cred.Credence.liar_fixed_point`, `Cred.Credence.neg_fixed_point_unique` — `0.5` fixed point and uniqueness
- `Cred.Credence.conj_disj_not_distrib` — `⊗` does not distribute over `⊔`

## Collapse Tower (orientation)

```
[0,1]  →  {0,½,1}  →  {0,1}  →  Classical (+material implication)
Cred      RM3-like    Relevant     (ex falso appears)
```

## Repo Layout

- `lean/` — Lean 4 formalization (authoritative for Part 1 definitions/theorems)
- `part1/` — paper + Part 1 notes (primitives and collapse connections)
- `part2/` — roadmap: graded mathematics as the primary setting
- `part3/` — roadmap: new proof techniques, undecidability, self-hosting

## Build

```bash
cd lean && lake build
cd part1 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
# fallback:
# cd part1 && pdflatex paper.tex && pdflatex paper.tex
```

## References

- Ramsey (1926), de Finetti (1937), Jaynes (2003) — credence foundations
- Rényi (1955), Popper (1959) — conditional probability as primitive
- Anderson & Belnap (1975) — relevant logic
