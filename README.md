# ProbTT: Type Theory with Primitive Probability

A type theory where **probability is primitive**, not derived. MLTT emerges as the {0,1}-fragment.

## The Idea

Traditional type theory:
```
Types → Propositions → Probability (constructed via measure theory)
```

ProbTT:
```
Prob (primitive) → Types, Propositions (derived as {0,1} case)
```

## Core Innovation: Probabilistic Judgments

Instead of `Γ ⊢ a : A`, we have:
```
Γ ⊢ a : A @ p     -- "a has type A with probability p"
```

When `p = 1`: ordinary typing. When `p ∈ (0,1)`: uncertain typing.

## Logic from Expectation

| Classical | ProbTT |
|-----------|--------|
| `∀x. P(x)` | `𝔼[P] = 1` |
| `∃x. P(x)` | `𝔼[P] > 0` |
| `P → Q` | `𝔼[Q \| P] = 1` |

## Status

- **Sketch**: `papers/probtt/probtt-sketch.tex`
- **Old Lean code**: `lean/` (axioms-in-MLTT approach, superseded)

The sketch defines:
- Probabilistic judgments
- Stochastic function types (Markov kernels)
- Probabilistic pairs and identity
- MLTT embedding theorem (the {0,1} case)

## Next Steps

1. Formalize rules precisely
2. Prove MLTT embedding rigorously
3. Prototype in Dedukti/Lambdapi
4. Study metatheory (normalization, consistency)

## Building

```bash
cd papers/probtt && pdflatex probtt-sketch.tex
```

## License

MIT
