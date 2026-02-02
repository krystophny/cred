# CredTT: Type Theory with Primitive Credences

A type theory where **credences are primitive**, not derived from numbers.

## Core Idea

Judgments carry credences: `Gamma |- a : A @ c`

The credence algebra is a **De Morgan algebra**:
```
0 : C           -- impossibility
1 : C           -- certainty
* : C -> C -> C -- multiplication (conjunction)
~ : C -> C      -- complement (negation)
<= : C -> C -> Prop
```

Disjunction is derived: `c1 | c2 = ~(~c1 * ~c2)`

## Key Rule

Credences multiply in elimination:
```
Gamma |- f : A -> B @ c1    Gamma |- a : A @ c2
-----------------------------------------------
           Gamma |- f a : B @ c1*c2
```

## Instances

| C | Interpretation |
|---|----------------|
| {0,1} | MLTT (classical logic) |
| [0,1] | Probability/confidence |
| [0,inf] | Costs |

## Key Features

- **MLTT as limit**: When C = {0,1}, CredTT collapses to Martin-Lof Type Theory
- **Conditioning**: Via chain rule `P(A,B) = P(A|B) * P(B)`, no division needed
- **Graded ex falso**: Continuous spectrum from constrained (c=1) to unconstrained (c=0)

## Files

```
papers/credtt/credtt.tex   -- The specification
CLAUDE.md                  -- Project documentation
TYPECHECKER.md             -- Implementation sketch
```

## Build

```bash
cd papers/credtt && pdflatex credtt.tex
```

## Status

Paper specification complete. Next: Agda formalization.

## Future Extension: ProbTT

ProbTT extends CredTT with addition (+) for marginalization:
- Marginalization: P(A) = sum_b P(A,b)
- This is probability-specific, not needed for base logic

## License

MIT
