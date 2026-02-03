# CLAUDE.md

## Build

```bash
cd lean && lake build              # Lean formalization
cd part1 && pdflatex paper.tex     # Paper (run twice for refs)
```

Lean 4.16.0 + mathlib4. Correctness = type-checking theorems.

## Current Milestone: Part 1

Complete the core Cred algebra with full Lean proofs and publication paper.

We use standard mathematics and Lean to reason about Cred. Self-hosting (Cred reasoning about itself) is a future goal.

## Primitives

```
[0,1]   credence values
0       impossibility
1       certainty
~c      negation (1 - c)
c₁⊗c₂   conjunction (product)
c₁⊔c₂   disjunction (De Morgan dual)
(A|B)   conditioning (primitive)
```

**Chain rule axiom**: (A|B)·B = A∧B

When B = 0: any value satisfies the equation. Conditioning is unconstrained — no ex falso.

## Key Results (Lean)

| Theorem | Statement |
|---------|-----------|
| `liar_fixed_point` | ~half = half |
| `neg_fixed_point_unique` | 0.5 is unique negation fixed point |
| `conditioning_zero_any` | No ex falso at 0 |
| `conj_disj_not_distrib` | ⊗ does not distribute over ⊔ |

## Structure

```
lean/Cred/Basic.lean   Core algebra + theorems
part1/paper.tex        Publication paper
part2/, part3/         Future: graded math, self-hosting
```

## Philosophy

**Inference constrains**: Evidence narrows possibilities from prior uncertainty. Impossible evidence (cred 0) provides no constraint.

**Conditional first**: Like set theory has only subsets (not unrestricted comprehension), we have only conditional credences as primitive.
