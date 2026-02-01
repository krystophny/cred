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

### vs Graded Type Theory (Granule/Gerty)

| Aspect | Graded types | ProbTT |
|--------|--------------|--------|
| Structure | Semiring (needs +) | De Morgan (just · and ¬) |
| Framing | MLTT + grades | Grades → MLTT |
| Interpretation | Resource usage | Probability/confidence |

### vs MLTT

ProbTT is MLTT with weights. MLTT is ProbTT restricted to W = {0,1}.

## Prior Art and Literature Context

### What Already Exists

**1. Pavelka-style Fuzzy Logic (Graded Provability)**

Pavelka (1979) and Hájek (1998) developed logics where provability has degrees:
- Degree of provability: `|φ|_T = sup{r | T ⊢ (φ, r)}`
- "True = provable to any degree below 1" is standard
- ProbTT's `Γ ⊢ A @ w` is very close to Pavelka's graded formulas `(φ, r)`

Key reference: Hájek, *Metamathematics of Fuzzy Logic* (1998)

**2. Self-Reference Fixed Points (w = ¬w → w = 1/2)**

The liar paradox in fuzzy logic yields fixed points at intermediate values:
- Hájek, Paris, Shepherdson, "The Liar Paradox and Fuzzy Logic" (JSL 2000)
- Shows how 1/2 arises as stable value under self-referential evaluation
- ProbTT's Gödel fixed point is in this tradition

**3. Logics of Formal Inconsistency (LFIs)**

da Costa's C-systems and LFIs have object-level consistency operators:
- `◦A` means "A is consistent"
- "Gentle explosion": from A, ¬A, and ◦A derive anything
- Without ◦A, contradiction doesn't explode
- ProbTT gates explosion by weight instead of a special connective

**4. Paraconsistent Fuzzy Logics**

Recent work (2024-2026) on degree-preserving Gödel logics with involutive negation:
- Graded non-explosion
- Careful study of negation/explosion behavior
- Close to ProbTT's "graded ex falso"

### What's New in ProbTT

The existing literature provides:
- ✓ Graded provability degrees
- ✓ Self-reference fixed points at 1/2
- ✓ Graded consistency notions
- ✓ Non-explosive contradiction handling

ProbTT's **novel contributions**:

1. **Dependent type theory packaging**: Π/Σ/Id interact with weights as first-class structure
2. **Weights primitive, MLTT as limit**: Not "MLTT + grades" but "grades → MLTT"
3. **Conditioning replaces implication**: No residuated implication, just multiplicative chain rule
4. **De Morgan algebra, not t-norm**: Minimal structure (just · and ¬, no +)

### Key Citations

| Topic | Primary Reference |
|-------|-------------------|
| Graded provability | Hájek 1998, Pavelka 1979 |
| Self-reference/liar | Hájek-Paris-Shepherdson 2000 |
| LFIs/paraconsistency | da Costa 1974, Carnielli-Coniglio 2016 |
| Degree-preserving logics | Recent work 2024-2026 |
| Graded type theory | Orchard et al. (Granule) |

### Positioning Summary

```
Fuzzy Logic (Pavelka/Hájek)     ProbTT             Graded Types (Granule)
         ↓                         ↓                        ↓
   Graded provability         Weights as           Resource-tracking
   + truth degrees            foundation           on MLTT
         ↓                         ↓                        ↓
   Standard implication       Conditioning         Semiring grades
   (residuum)                 (multiplicative)     (needs +)
```

ProbTT takes the graded provability insights from fuzzy logic and rebuilds dependent type theory from scratch, with conditioning (not implication) as the fundamental connective.

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
