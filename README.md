# Cred: A Credence Algebra

**Credence** = degree of belief, a value in [0,1]. Standard in Bayesian epistemology (Ramsey, de Finetti, Jaynes).

## Why Not Just Probability?

| Standard Probability | Cred |
|---------------------|------|
| P(A\|B) = P(A∧B)/P(B) — undefined at 0 | Chain rule primitive: cred(A\|B)·cred(B) = cred(A∧B) |
| Conditioning at 0: undefined | Conditioning at 0: unconstrained (no ex falso) |
| Collapses to classical logic | Collapses to relevant logic |

## The Algebra

```
Values:  [0,1]
Negation:    ~c = 1 - c
Conjunction: c₁ ⊗ c₂ = c₁·c₂
Disjunction: c₁ ⊔ c₂ = c₁ + c₂ - c₁·c₂
Conditioning: (A|B)·B = A∧B  (primitive)
```

When B = 0, chain rule becomes x·0 = 0, satisfied by any x. No forced value — no ex falso.

## Key Properties

- **Fixed points for paradoxes**: Liar sentence L ≡ ¬L gives cred(L) = 0.5
- **0.5 = maximal uncertainty**: Flat prior over {true, false}
- **Relevant collapse**: Binary Cred → relevant logic (not classical)

## Collapse Hierarchy

```
[0,1]  →  {0,½,1}  →  {0,1}  →  Classical
Cred      RM3-like    Relevant   (+ex falso)
```

## Current Milestone: Part 1

Formalize the core algebra with machine-checked proofs and a publication-quality paper.

- `lean/` — Lean 4 formalization (mathlib4)
- `part1/paper.tex` — LaTeX paper

```bash
cd lean && lake build              # Build Lean
cd part1 && pdflatex paper.tex     # Build paper
```

## References

- Ramsey (1926), de Finetti (1937), Jaynes (2003) — credence foundations
- Rényi (1955), Popper (1959) — conditional probability as primitive
- Anderson & Belnap (1975) — relevant logic
