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
```

## Philosophy: Inference as Constraint

**Inference narrows possibilities from uncertainty, not builds certainties from nothing.**

In the Bayesian philosophy (Jaynes, de Finetti, Cox):
- **Prior**: Maximal uncertainty—flat distribution over possibilities
- **Evidence constrains**: Narrows the space of consistent beliefs
- **Posterior**: Prior + constraints
- **No evidence = no constraint**: Credence 0 evidence provides nothing to constrain with

This is why:
- **Conditioning is primitive**: Inference IS constraining belief by evidence
- **No ex falso**: Impossible evidence provides no constraint (not "everything follows")
- **0.5 = maximal uncertainty**: Flat prior over {true, false}
- **Chain rule**: (A|B)·B = A∧B expresses constraint propagation

## Why Graded?

| Binary Logic | Cred |
|--------------|------|
| Undecidable = stuck, no value | Undecidable = credence 0.5 |
| Paradoxes break the system | Paradoxes → fixed points |
| Gödel: true but unprovable | Gödel: credence 0.5 (meaningful) |
| Ex falso: nonsense follows | No ex falso: relevance preserved |

## Limiting Cases (Known Systems)

When we DO collapse to binary, we land in **relevant logic**, not classical:

```
Cred [0,1]          graded (where we work)
    ↓ collapse
{0, ½, 1}           three-valued relevant (RM3-like)
    ↓ collapse
{0, 1}              Boolean relevant logic (R, E)
    ↓ + ex falso
Classical FOL       (requires extra axiom)
```

**Key insight**: Cred generalizes **relevant logic**. Fuzzy logic generalizes **classical logic**. These are different!

```
Fuzzy ──generalizes──→ Classical (has ex falso)
                            ↑ DIFFERENT
Cred ──generalizes──→ Relevant (no ex falso)
```

## Defying Gödel

Gödel's incompleteness: "Some true statements are unprovable."

In binary logic, this is a fundamental limitation — statements exist in limbo.

In Cred:
- Gödel sentence G has credence **exactly 0.5**
- This IS a value. G is not stuck — it has graded truth.
- Self-reference produces fixed points, not paradoxes

**Cred makes undecidability a feature, not a bug.**

## Self-Hosting

Goal: Implement Cred in Cred itself.

Since Cred handles self-reference via fixed points (not paradoxes), self-hosting becomes natural. The system can reason about itself without the Gödelian limitations that plague binary foundations.

## Structure

- **part1/**: The primitives and collapse hierarchy
- **part2/**: Graded mathematics — where we live
- **part3/**: New techniques, undecidability, and self-hosting

## Prior Art

| Source | Contribution | Our use |
|--------|--------------|---------|
| **Jaynes (1957, 2003)** | Maximum entropy, probability as logic | Inference as constraint philosophy |
| **Shore & Johnson (1980)** | Uniqueness of entropy for constraint inference | Theoretical foundation |
| **de Finetti (1937)** | Coherence, exchangeability | Constraint consistency |
| **Rényi (1955)** | Conditional probability as primitive | Chain rule axiom |
| **Popper (1959)** | Primitive conditional probability | Alternative to division |
| **van Fraassen (1983)** | Probabilistic semantics for relevant logic | Semantic correspondence |
| **Anderson & Belnap (1960s)** | Relevant logic (no ex falso) | Boolean collapse target |
| **RM3** | Three-valued relevant logic | {0, ½, 1} collapse target |
| **Walley (1991)** | Imprecise probability, credal sets | Constraint regions |
| **Brady, Weber** | Paraconsistent mathematics | Related approach |
| **Markov categories (2020)** | Conditioning without division | Categorical connection |
