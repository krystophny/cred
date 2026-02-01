# CLAUDE.md

## Project Overview

**ProbTT**: A type theory where weights are primitive, not derived from numbers.

The key insight: types and logic EMERGE from weight structure. MLTT is the {0,1} limiting case.

## The Hierarchy

```
Weight algebra: (0, 1, ·, ¬, ≤)     ← PRIMITIVE
        ↓ defines behavior of
Type formers: ×, +, →, Π, Σ, Id
        ↓ restricts to {0,1}
MLTT (Martin-Löf Type Theory)
        ↓ propositions-as-types
First-order logic
        ↓ restricts to decidable
Classical logic
```

Everything derives from the weight structure.

## Weight Algebra

### Minimal Structure (Product De Morgan Algebra)

```
W = (0, 1, ·, ¬, ≤)

0 : W                  -- impossibility
1 : W                  -- certainty
· : W → W → W          -- multiplication (conjunction)
¬ : W → W              -- complement, ¬w = 1 - w (negation)
≤ : W → W → Prop       -- ordering
```

### Derived Operations

```
w ∨ v := ¬(¬w · ¬v)    -- De Morgan OR
      = w + v - w·v    -- probabilistic sum (inclusion-exclusion)
```

### What We DON'T Need

- **No addition (+)**: OR derived via De Morgan
- **No subtraction (-)**: Only complement ¬w = 1-w
- **No division (/)**: Chain rule is multiplicative

### Axioms (12 total)

Multiplication:
```
w · 1 = w                    -- unit
w · 0 = 0                    -- annihilation
(u · v) · w = u · (v · w)    -- associativity
u · v = v · u                -- commutativity
```

Complement:
```
¬0 = 1                       -- complement of zero
¬1 = 0                       -- complement of one
¬¬w = w                      -- involution
```

Order:
```
w ≤ w                        -- reflexivity
u ≤ v ∧ v ≤ w → u ≤ w        -- transitivity
u ≤ v ∧ v ≤ u → u = v        -- antisymmetry
0 ≤ w                        -- zero least
w ≤ 1                        -- one greatest
```

## Judgments

```
Γ ⊢ a : A @ w
```

Meaning: term `a` has type `A` with weight `w`.

- `w = 1`: definitely inhabits
- `w = 0`: does not inhabit (vacuously true)
- `0 < w < 1`: partially/probably inhabits

## Key Rules

### Weights Multiply in Elimination

```
Γ ⊢ f : A → B @ w    Γ ⊢ a : A @ v
──────────────────────────────────
        Γ ⊢ f a : B @ w · v
```

### Type Formers from Weight Operations

| Type | Weight behavior | {0,1} case |
|------|-----------------|------------|
| A × B | w · v | Boolean AND |
| A + B | (via De Morgan) | Boolean OR |
| ¬A | ¬w | Boolean NOT |
| A → B | function, weight multiplies | Implication |

## Conditioning (Not Implication!)

### Why No Material Implication

Material implication A → B = ¬A ∨ B has paradoxes:
- "False implies anything" = True (weird!)

### Chain Rule Instead

```
P(A,B) = P(A|B) · P(B)
```

Relates joint, marginal, and conditional. Pure multiplication, no division.

### Conditioning vs Implication

| Concept | What it is | False antecedent |
|---------|------------|------------------|
| A → B (logic) | ¬A ∨ B, truth-functional | "True" (lies) |
| P(A\|B) (probability) | P(A,B)/P(B), needs joint | Indeterminate (honest) |

We use conditioning. It doesn't have the paradoxes.

## Graded Ex Falso

Classical ex falso: ⊥ → A (from false, anything follows)

Probabilistic ex falso: When P(B) = 0, any P(A|B) satisfies the chain rule.

**This is a continuous phenomenon:**

| P(B) | Constraint on P(A\|B) |
|------|----------------------|
| 1 | Fully determined |
| ε (small) | Weakly constrained |
| 0 | Unconstrained (ex falso) |

Classical logic has only the endpoints. ProbTT has the entire spectrum.

## What We Get

### Without + (just · and ¬)

- Full propositional logic (AND, OR, NOT)
- First-order logic (∀, ∃ via infinite ·/∨)
- Bayes chain rule
- Conditioning

### Would Need + For

- Marginalization: P(A) = Σ_b P(A,b)
- This is probability-specific, not needed for FOL

## Relationship to Existing Systems

### vs Product Fuzzy Logic

| Aspect | Product fuzzy logic | ProbTT |
|--------|---------------------|--------|
| Weight algebra | Same (·, ¬) | Same |
| Conditioning | No | Yes (chain rule) |
| Type theory | No | Yes (Π, Σ, Id) |
| MLTT as limit | No | Yes |

ProbTT = Product fuzzy logic + conditioning + type theory

### vs Graded Type Theory (Granule/Gerty)

| Aspect | Graded types | ProbTT |
|--------|--------------|--------|
| Structure | Semiring (needs +) | De Morgan (just · and ¬) |
| Framing | MLTT + grades | Grades → MLTT |
| Interpretation | Resource usage | Probability/confidence |

### vs MLTT

ProbTT is MLTT with weights. MLTT is ProbTT restricted to W = {0,1}.

## File Structure

```
papers/
  probtt/
    probtt.tex    -- The specification (main document)
    probtt.pdf    -- Built paper
```

## Build

```bash
cd papers/probtt && pdflatex probtt.tex
```

## Current Status

Paper complete with:
- Weight algebra (minimal)
- All type formers (Π, Σ, +, Id)
- Markov structure (copy, delete)
- Chain rule (multiplicative Bayes)
- MLTT embedding theorem
- Graded ex falso

## Open Problems

1. **Implementation**: Type checker for ProbTT
2. **Weight inference**: Can we infer weights from term structure?
3. **Continuous types**: Extension to measurable spaces
4. **Dependent weights**: w(x) varying over x in (x:A) → B @ w(x)
