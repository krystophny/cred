# Cred Lean Formalization

Machine-verified proofs for the Cred credence algebra.

## Building

```bash
lake build
```

## Structure

- `Cred/Basic.lean` - Core credence algebra (562 lines)
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
