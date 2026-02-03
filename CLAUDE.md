# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build & Test Commands

### Lean Formalization (Primary)
```bash
cd lean && lake build          # Build the Cred library
cd lean && lake clean && lake build   # Full rebuild
```
- Toolchain: Lean v4.16.0 with mathlib4 v4.16.0
- Tests: No explicit test suite; correctness verified by type-checking theorems

### LaTeX Paper
```bash
cd part1 && pdflatex paper.tex   # Build paper (run twice for refs)
cd part1 && latexmk -pdf paper.tex   # Alternative with latexmk
```

### CI Jobs
- **Lean**: `lake build` in `lean/` (ACTIVE)
- **Agda**: `agda Everything.agda` in `agda/` (dormant - directory planned)
- **OCaml**: `dune build && dune runtest` in `credtt-impl/` (dormant - directory planned)
- **LaTeX**: builds `papers/credtt/credtt.tex` (dormant - path differs from part1/)

## Project Overview

**Cred**: A foundation for graded mathematics. Credences in [0,1] are the primary setting, not a generalization of binary logic. Binary logic {0,1} is a degenerate special case.

## Philosophy: Inference as Constraint

**Core principle**: Inference narrows possibilities from uncertainty toward specificity, not builds certainties from nothing.

In the Bayesian view (Jaynes, de Finetti, Cox):
- **Prior**: Start with maximal uncertainty—a flat or broad distribution over possibilities
- **Evidence constrains**: Each piece of evidence narrows the space of consistent beliefs
- **Posterior**: The result of applying all constraints to the prior
- **No evidence = no constraint**: When evidence has credence 0, it provides no information to constrain belief

This explains Cred's key features:
- **Conditioning is primitive** because inference IS conditioning—evidence constrains belief via the chain rule
- **No ex falso** because impossible evidence (B=0) provides no constraint; you cannot narrow possibilities with vacuous information
- **0.5 as maximal uncertainty** represents a flat prior over {true, false}; the Gödel/liar sentence at 0.5 means "maximally unconstrained"
- **Chain rule is fundamental**: (A|B)·B = A∧B says "constrained belief × constraining evidence = joint"

This aligns with:
- **Jaynes' Maximum Entropy**: Use the least informative distribution consistent with known constraints
- **Shore-Johnson Axioms**: Entropy maximization is the unique consistent method for constraint-based inference
- **Rényi/Popper**: Conditional probability as primitive, not derived via division
- **de Finetti's Coherence**: Probability assignments must be self-consistent under all constraints
- **Walley's Imprecise Probability**: Credal sets as constraint regions bounding feasible beliefs

### The "Conditional First" Principle

Conditioning is more fundamental than absolute assignment—paralleling set theory:
- **Set theory**: Only subsets of sets, not unrestricted comprehension (avoids Russell's paradox)
- **Probability**: Only conditional credences primitive; absolute credence = cred(A|Ω)
- **Logic**: No ex falso; conditioning on impossibility is unconstrained, not "everything follows"

## Architecture

```
foundations/
├── lean/                    # ACTIVE: Lean 4 formalization
│   ├── Cred/Basic.lean      # Core credence algebra (441 lines, 50+ theorems)
│   ├── Cred.lean            # Root module
│   └── lakefile.toml        # Lake build config
├── part1/                   # Primitives + collapse hierarchy
│   └── paper.tex            # Publication-quality paper (~13 pages)
├── part2/                   # Graded mathematics (markdown specs)
└── part3/                   # Self-hosting, undecidability (markdown specs)
```

## Lean Formalization Structure

`lean/Cred/Basic.lean` implements:

| Component | Description |
|-----------|-------------|
| `Credence` | Real in [0,1] with bounds proofs |
| `~c` (negation) | 1 - c |
| `c₁ ⊗ c₂` (conjunction) | Product (assumes independence) |
| `c₁ ⊔ c₂` (disjunction) | De Morgan dual: c₁ + c₂ - c₁*c₂ |
| `Conditioning` | Primitive structure with chain rule axiom |
| `half` | The 0.5 credence (negation fixed point) |

Key theorems proven:
- `liar_fixed_point`: ~half = half (self-reference gives 0.5)
- `neg_fixed_point_unique`: 0.5 is the unique negation fixed point
- `conj_disj_not_distrib`: Conjunction doesn't distribute over disjunction
- `contradiction_le_quarter`: c ⊗ ~c ≤ 0.25 (max uncertainty at 0.5)
- `conditioning_zero_any`: No ex falso - conditioning on 0 is unconstrained

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

### Conditioning (Key Innovation)

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

## Collapse Hierarchy

When collapsing to binary, Cred lands in relevant logic (not classical):
```
Cred [0,1]          graded (where we work)
    ↓ collapse
{0, ½, 1}           three-valued relevant (RM3-like)
    ↓ collapse
{0, 1}              Boolean relevant logic (R, E)
    ↓ + ex falso
Classical FOL       (requires extra axiom)
```

## Open Research (GitHub Issues)

Active meta-issues:
- #260: Prove Three-Valued Cred ≡ RM3
- #254: Prove Boolean Cred ≡ Relevant Logic R
- #215: Substitution lemma postulates at lift levels 6-7
- #186-187: Progress and preservation theorems for CredTT
