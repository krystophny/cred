# Cred Lean Formalization

Machine-verified proofs for the Cred credence algebra. This Lean library is the authoritative source for Part 1: the paper (`part1/paper.tex`) should match the definitions and theorem statements here.

Project goal (beyond Part 1): use this algebra as a foundation for graded mathematics and new proof techniques where propositions and proofs can take values in `[0,1]`.

## Building

```bash
lake build
```

## Structure

- `Cred/Basic.lean` - Core credence algebra
  - Credence type with [0,1] bounds
  - Negation, conjunction, disjunction operations
  - Conditioning via chain rule (primitive)
  - Fixed point theorems (liar sentence)
  - Three-valued collapse to RM3

## Key Theorems

| Theorem | Description |
|---------|-------------|
| `neg_neg` | Negation is involutive |
| `conditioning_zero_any` | Conditioning on 0 is unconstrained (no ex falso) |
| `conditioning_unique` | Conditioning is unique when evidence > 0 |
| `liar_fixed_point` | 0.5 is a negation fixed point |
| `neg_fixed_point_unique` | 0.5 is the unique negation fixed point |
| `conj_disj_not_distrib` | Conjunction does not distribute over disjunction |

## Dependencies

- Lean 4 (see lean-toolchain)
- Mathlib 4.16.0
