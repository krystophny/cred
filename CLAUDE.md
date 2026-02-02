# CLAUDE.md

## Project Overview

**Cred**: A foundation for mathematics where credences are primitive and logic emerges.

## Core Architecture

```
Credence Algebra (*, ~, ≤, _|_)     ← PRIMITIVE
         ↓
Graded Propositions (P : C)
         ↓
Graded Predicates (S : Thing → C)
         ↓ Boolean collapse
Relevant Logic (no ex falso)
         ↓ add material implication
Classical FOL
```

## The Primitive Structure

```
C : credence values [0,1]
0 : impossibility
1 : certainty
* : conjunction (multiplication)
~ : negation (complement, ~c = 1 - c)
≤ : ordering
_|_ : conditioning (PRIMITIVE, not derived from division)
```

## Conditioning (The Key Innovation)

NOT defined via division:
```
P(A|B) := P(A∧B) / P(B)     ← requires division, undefined at 0
```

Instead, PRIMITIVE with chain rule axiom:
```
(A | B) * B = A ∧ B         ← only multiplication, unconstrained at 0
```

When B = 0: (A | 0) is unconstrained (not "true" like material implication).

This avoids ex falso naturally.

## Collapse Hierarchy

```
Cred [0,1]          graded relevant (primary)
    ↓
{0, ½, 1}           three-valued relevant (RM3-like)
    ↓
{0, 1}              Boolean relevant logic
    ↓ +ex falso
Classical FOL       (optional extension)
```

## What Emerges vs What's Assumed

| Assumed (Primitive) | Emerges |
|---------------------|---------|
| Credence values C | Propositions (as credences) |
| Operations *, ~, ≤ | Logical connectives |
| Conditioning _\|_ | Inference rules |
| Chain rule axiom | Relevant logic (Boolean collapse) |

## Key Properties

1. **No ex falso**: From impossible condition, nothing determined (not "everything true")
2. **Graded truth**: Undecidability visible as intermediate credence
3. **Relevant logic emerges**: Boolean collapse gives relevant logic, not classical
4. **Probability-native**: Chain rule is probabilistic reasoning

## File Structure

```
foundations/
├── part1/          Collapse hierarchy
├── part2/          Credence foundation (no crisp sets)
├── part3/          New proof techniques, undecidability
└── README.md
```

## Comparison to Related Work

| System | Relationship |
|--------|--------------|
| Fuzzy logic | Different: fuzzy collapses to classical (has ex falso) |
| Relevant logic | Cred generalizes relevant logic |
| Probability theory | Similar: conditioning undefined at 0 |
| Paraconsistent logic | Related: no explosion from contradiction |

## Key Insight

Classical logic is a **lossy compression** of credence structure:
1. Collapse [0,1] to {0,1} (lose graded truth)
2. Add ex falso (lose relevance)

Cred is what you get before these losses.
