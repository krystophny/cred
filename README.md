# Cred: A Foundation for Graded Mathematics

**Cred** is a foundation for mathematics where credences are primitive. We work directly with graded truth — not as a generalization of binary logic, but as the natural setting for mathematics.

## The Vision

**Graded mathematics is primary. Binary logic is a degenerate special case.**

```
Cred [0,1]              ← WHERE WE WORK
├── Graded propositions
├── Graded predicates (non-crisp sets)
├── Graded proofs
└── Self-hosting Cred in Cred

Binary {0,1}            ← FALLBACK (compatibility only)
└── Classical logic/sets (recoverable if needed)
```

## Why Graded?

| Binary Logic | Cred |
|--------------|------|
| Undecidable = stuck, no value | Undecidable = credence 0.5 |
| Paradoxes break the system | Paradoxes → fixed points |
| Gödel: true but unprovable | Gödel: credence 0.5 (meaningful) |
| Ex falso: nonsense follows | No ex falso: relevance preserved |

## Defying Gödel

Gödel's incompleteness: "Some true statements are unprovable."

In binary logic, this is a fundamental limitation — statements exist in limbo.

In Cred:
- "Unprovable" means credence doesn't reach 1
- Gödel sentence G has credence **exactly 0.5**
- This IS a value. G is not stuck — it has graded truth.
- Self-reference produces fixed points, not paradoxes

**Cred makes undecidability a feature, not a bug.**

## Self-Hosting

Goal: Implement Cred in Cred itself.

Since Cred handles self-reference via fixed points (not paradoxes), self-hosting becomes natural. The system can reason about itself without the limitations that plague binary foundations.

## Structure

- **part1/**: The primitives (and collapse to binary for compatibility)
- **part2/**: Graded mathematics — where we live
- **part3/**: New techniques, undecidability, and self-hosting

## Prior Art

- **Rényi (1955)**: Conditional probability as primitive
- **Anderson & Belnap (1960s)**: Relevant logic
- **Paraconsistent mathematics**: Brady, Weber
