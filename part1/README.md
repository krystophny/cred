# Part 1: The Primitives

The foundational structure of Cred, plus collapse to binary (for compatibility only).

## The Primitives

```
C = [0, 1]              credence values
0, 1                    impossibility, certainty
*                       conjunction (multiplication)
~                       negation (complement)
≤                       ordering
_|_                     conditioning (chain rule)
```

## Why These Primitives?

- **Multiplication (*)**: Credences compound — uncertainty multiplies
- **Complement (~)**: ~c = 1 - c, natural negation
- **Conditioning (_|_)**: Via chain rule, NOT division — avoids ex falso

## The Chain Rule

```
(A | B) * B = A ∧ B
```

When B = 0: (A | 0) is unconstrained. No ex falso.

## Files

- `01-credence-algebra.md` — The algebraic structure
- `02-conditioning.md` — Chain rule vs division (Rényi's insight)
- `03-three-valued.md` — {0, ½, 1} intermediate (for reference)
- `04-boolean-relevant.md` — {0, 1} collapse gives relevant logic
- `05-classical.md` — Adding ex falso (NOT recommended)

## Collapse (Compatibility Only)

We CAN collapse to binary if needed for classical compatibility:

```
Cred [0,1] → {0, ½, 1} → {0, 1} → Relevant logic
```

**But we prefer to stay in [0,1].** The collapse is documented for:
- Showing we recover known structures
- Interfacing with classical mathematics when necessary
- Understanding the relationship to existing foundations

**Graded is primary. Binary is fallback.**
