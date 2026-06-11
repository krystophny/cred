# Part 1: The Primitives

Part 1 establishes the primitive Cred algebra that the rest of the project builds on. The immediate goal is a clean, publication-quality account (`part1/paper.tex`) aligned with the machine-checked Lean source (`lean/Cred/Basic.lean`).

This is intentionally the smallest layer: primitives + their core consequences, plus collapse connections to known systems (for orientation). Graded mathematics and new proof techniques are developed in later parts.

## The Primitives

```
C = [0, 1]              credence values
0, 1                    impossibility, certainty
⊗                       conjunction (product / multiplication on values)
~                       negation (complement)
≤                       ordering
_|_                     conditioning (chain rule)
```

## Why These Primitives?

- **Product (⊗)**: Credences compound; uncertainty multiplies
- **Complement (~)**: ~c = 1 - c, natural negation
- **Conditioning (_|_)**: via chain rule, not division; avoids ex falso

## The Chain Rule

```
cred(A|B) ⊗ cred(B) = cred(A ∧ B)
```

When B = 0: (A | 0) is unconstrained. No ex falso.

## Files

- `paper.tex`: publication paper (authoritative exposition for Part 1)

## The Collapse Tower (Limiting Cases)

**We work in Cred [0,1]. These collapses show connections to known systems.**

```
┌─────────────────────────────────────────────┐
│  Cred [0,1]           ← WHERE WE WORK       │
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
│  Relevant logic (R, E, RM)                  │
│  No ex falso                                │
└─────────────────────┬───────────────────────┘
                      │ add material implication
                      ▼
┌─────────────────────────────────────────────┐
│  Classical FOL                              │
│  Material implication: A → B = ¬A ∨ B       │
│  Ex falso holds: ⊥ → A                      │
└─────────────────────────────────────────────┘
```

## Key Relationships

| Cred collapses to... | Known system | Key property |
|---------------------|--------------|--------------|
| {0, ½, 1} | RM3, Kleene-like | Three-valued relevant |
| {0, 1} | Relevant logic (R, E) | No ex falso |
| {0, 1} + ex falso | Classical FOL | Standard foundation |

## Two Generalizations

- **Cred generalizes relevant logic** (not classical, not fuzzy)
- **Fuzzy logic generalizes classical** (has ex falso)
- These are DIFFERENT generalizations

```
                    Fuzzy logic ←── generalizes ──→ Classical (ex falso)
                         ↑
                    DIFFERENT
                         ↓
                    Cred ←── generalizes ──→ Relevant logic (no ex falso)
```

## Prior Art for Limiting Cases

| System | Source | Our connection |
|--------|--------|----------------|
| RM3 | 3-valued relevant logic | {0, ½, 1} collapse |
| R, E | Anderson & Belnap (1960s) | {0, 1} collapse |
| Paraconsistent | Brady, Weber | Related (no explosion) |

**Graded is primary. These are limiting cases showing we land in known, well-studied territory.**
