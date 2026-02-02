# Part 1: The Collapse Hierarchy

How classical structures emerge from Cred as limiting cases.

## The Tower

```
┌─────────────────────────────────────────────┐
│  Cred [0,1]                                 │
│  Full graded credences                      │
│  Conditioning primitive (chain rule)        │
│  No ex falso, graded truth                  │
└─────────────────────┬───────────────────────┘
                      │ collapse (0,1) → ½
                      ▼
┌─────────────────────────────────────────────┐
│  Three-Valued {0, ½, 1}                     │
│  True / Unknown / False                     │
│  RM3-like relevant logic                    │
│  No ex falso, unknown propagates            │
└─────────────────────┬───────────────────────┘
                      │ collapse ½ → {0 or 1}
                      ▼
┌─────────────────────────────────────────────┐
│  Boolean Relevant {0, 1}                    │
│  True / False                               │
│  Relevant logic (R, E)                      │
│  No ex falso                                │
└─────────────────────┬───────────────────────┘
                      │ add material implication
                      ▼
┌─────────────────────────────────────────────┐
│  Classical FOL                              │
│  Material implication: A → B = ¬A ∨ B       │
│  Ex falso holds: ⊥ → A                      │
│  Standard foundation                        │
└─────────────────────────────────────────────┘
```

## Files

- `01-credence-algebra.md` - The primitive structure
- `02-conditioning.md` - Chain rule vs division
- `03-three-valued.md` - The RM3-like intermediate
- `04-boolean-relevant.md` - Relevant logic emerges
- `05-classical.md` - Adding ex falso (optional)
