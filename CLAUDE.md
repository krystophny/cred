# CLAUDE.md

## Project Overview

**Cred**: A foundation for graded mathematics. We work in [0,1] credences as the primary setting, not as a generalization of binary logic.

## Core Vision

```
Cred [0,1]                    ← PRIMARY (where we live)
├── Graded propositions
├── Graded predicates (non-crisp sets)
├── Graded proofs
├── Self-hosting Cred in Cred
│
└── Boolean {0,1}             ← FALLBACK (compatibility only)
```

**Binary logic is a degenerate case, not the foundation.**

## The Primitive Structure

```
C : credence values [0,1]
0 : impossibility
1 : certainty
* : conjunction (multiplication)
~ : negation (complement, ~c = 1 - c)
≤ : ordering
_|_ : conditioning (PRIMITIVE, chain rule)
```

## Conditioning (The Key Innovation)

PRIMITIVE with chain rule axiom:
```
(A | B) * B = A ∧ B
```

When B = 0: (A | 0) is unconstrained — no ex falso.

## Why Graded is Primary

| Binary Logic | Cred |
|--------------|------|
| Undecidable = stuck | Undecidable = cred 0.5 (a value!) |
| Paradoxes break system | Paradoxes → fixed points |
| Gödel: unprovable limbo | Gödel: cred 0.5 (meaningful) |
| Self-reference problematic | Self-reference natural |

## Defying Gödel

Gödel's incompleteness is a limitation of BINARY logic:
- "True but unprovable" = stuck in limbo

In Cred:
- Gödel sentence G has cred(G) = 0.5
- This IS its truth value — not stuck
- Self-reference gives fixed points, not paradoxes

## Self-Hosting Goal

Implement Cred in Cred itself.

Since Cred handles self-reference via fixed points:
- The system can reason about itself
- No Gödelian limitations on self-description
- True foundational autonomy

## File Structure

```
foundations/
├── part1/    Primitives (+ collapse for compatibility)
├── part2/    Graded mathematics (PRIMARY)
├── part3/    New techniques, undecidability, self-hosting
└── README.md
```

## Key Properties

1. **Graded truth primary**: [0,1] is where we work, not {0,1}
2. **No ex falso**: Conditioning, not material implication
3. **Undecidability has value**: cred = 0.5, not "stuck"
4. **Self-reference works**: Fixed points, not paradoxes
5. **Self-hosting possible**: System can describe itself

## Collapse (For Compatibility Only)

If needed for classical mathematics:
```
Cred [0,1] → {0,1} Boolean → Relevant logic
```

But we prefer to stay graded.
