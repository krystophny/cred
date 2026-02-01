# ProbTT: Type Theory with Primitive Weights

A type theory where **weights are primitive**, not derived from numbers.

## Core Idea

Judgments carry weights: `Γ ⊢ a : A @ w`

The weight algebra is a **De Morgan algebra**:
```
0 : W           -- impossibility
1 : W           -- certainty
· : W → W → W   -- multiplication (conjunction)
¬ : W → W       -- complement (negation)
≤ : W → W → Prop
```

Disjunction is derived: `w ∨ v = ¬(¬w · ¬v)`

## Key Rule

Weights multiply in elimination:
```
Γ ⊢ f : A → B @ w    Γ ⊢ a : A @ v
──────────────────────────────────
       Γ ⊢ f a : B @ w·v
```

## Instances

| W | Interpretation |
|---|----------------|
| {0,1} | MLTT (classical logic) |
| [0,1] | Probability |
| [0,∞] | Costs |

## Key Features

- **MLTT as limit**: When W = {0,1}, ProbTT collapses to Martin-Löf Type Theory
- **Conditioning**: Via chain rule `P(A,B) = P(A|B) · P(B)`, no division needed
- **Graded ex falso**: Continuous spectrum from constrained (w=1) to unconstrained (w=0)

## Files

```
papers/probtt/probtt.tex   -- The specification
CLAUDE.md                  -- Project documentation
TYPECHECKER.md             -- Implementation sketch
```

## Build

```bash
cd papers/probtt && pdflatex probtt.tex
```

## Status

Paper specification complete. Next: Agda formalization.

## License

MIT
