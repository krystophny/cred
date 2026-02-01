# ProbTT: Type Theory with Primitive Weights

A type theory where **weights are primitive**, not numbers.

## Core Idea

Judgments carry weights: `Γ ⊢ a : A @ w`

The weight monoid W has:
```
1 : W           -- certainty
0 : W           -- impossibility
· : W → W → W   -- combination
≤ : W → W → Prop
```

**No addition. No subtraction. No numbers assumed.**

## Key Rule

Weights multiply in elimination:
```
Γ ⊢ f : A → B @ w    Γ ⊢ a : A @ v
────────────────────────────────────
       Γ ⊢ f a : B @ w·v
```

## Instances

| W | Interpretation |
|---|----------------|
| {0,1} | MLTT (classical) |
| [0,1] | Probability |
| [0,∞] | Costs |

## Files

```
papers/probtt/probtt.tex   -- The specification
```

## Build

```bash
cd papers/probtt && pdflatex probtt.tex
```

## Status

Minimal specification complete. Next: examples, prototype, metatheory.

## License

MIT
