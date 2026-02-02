# CLAUDE.md

## Project Overview

**CredTT**: A type theory where credences are primitive, not derived from numbers.

The key insight: types and logic EMERGE from credence structure. MLTT is the {0,1} limiting case.

## The Hierarchy

```
Credence algebra: (0, 1, *, ~, <=)     <- PRIMITIVE
        | defines behavior of
Type formers: x, +, ->, Pi, Sigma, Id
        | restricts to {0,1}
MLTT (Martin-Lof Type Theory)
        | propositions-as-types
First-order logic
        | restricts to decidable
Classical logic
```

Everything derives from the credence structure.

## Credence Algebra

### Minimal Structure (Product De Morgan Algebra)

```
C = (0, 1, *, ~, <=)

0 : C                  -- impossibility
1 : C                  -- certainty
* : C -> C -> C        -- multiplication (conjunction)
~ : C -> C             -- complement, ~c = 1 - c (negation)
<= : C -> C -> Prop    -- ordering
```

### Derived Operations

```
c1 | c2 := ~(~c1 * ~c2)   -- De Morgan OR
        = c1 + c2 - c1*c2 -- probabilistic sum (inclusion-exclusion)
```

### What We DON'T Need

- **No addition (+)**: OR derived via De Morgan
- **No subtraction (-)**: Only complement ~c = 1-c
- **No division (/)**: Chain rule is multiplicative

### Axioms (12 total)

Multiplication:
```
c * 1 = c                    -- unit
c * 0 = 0                    -- annihilation
(a * b) * c = a * (b * c)    -- associativity
a * b = b * a                -- commutativity
```

Complement:
```
~0 = 1                       -- complement of zero
~1 = 0                       -- complement of one
~~c = c                      -- involution
```

Order:
```
c <= c                       -- reflexivity
a <= b and b <= c -> a <= c  -- transitivity
a <= b and b <= a -> a = b   -- antisymmetry
0 <= c                       -- zero least
c <= 1                       -- one greatest
```

## Judgments

```
Gamma |- a : A @ c
```

Meaning: term `a` has type `A` with credence `c`.

- `c = 1`: definitely inhabits
- `c = 0`: does not inhabit (vacuously true)
- `0 < c < 1`: partially/probably inhabits

## Key Rules

### Credences Multiply in Elimination

```
Gamma |- f : A -> B @ c1    Gamma |- a : A @ c2
-----------------------------------------------
          Gamma |- f a : B @ c1 * c2
```

### Type Formers from Credence Operations

| Type | Credence behavior | {0,1} case |
|------|-------------------|------------|
| A x B | c1 * c2 | Boolean AND |
| A + B | (via De Morgan) | Boolean OR |
| ~A | ~c | Boolean NOT |
| A -> B | function, credence multiplies | Implication |

## Conditioning (Not Implication!)

### Why No Material Implication

Material implication A -> B = ~A | B has paradoxes:
- "False implies anything" = True (weird!)

### Chain Rule Instead

```
P(A,B) = P(A|B) * P(B)
```

Relates joint, marginal, and conditional. Pure multiplication, no division.

### Conditioning vs Implication

| Concept | What it is | False antecedent |
|---------|------------|------------------|
| A -> B (logic) | ~A | B, truth-functional | "True" (lies) |
| P(A\|B) (probability) | P(A,B)/P(B), needs joint | Indeterminate (honest) |

We use conditioning. It doesn't have the paradoxes.

## Graded Ex Falso

Classical ex falso: bot -> A (from false, anything follows)

Probabilistic ex falso: When P(B) = 0, any P(A|B) satisfies the chain rule.

**This is a continuous phenomenon:**

| P(B) | Constraint on P(A\|B) |
|------|----------------------|
| 1 | Fully determined |
| epsilon (small) | Weakly constrained |
| 0 | Unconstrained (ex falso) |

Classical logic has only the endpoints. CredTT has the entire spectrum.

## What We Get

### Without + (just * and ~)

- Full propositional logic (AND, OR, NOT)
- First-order logic (forall, exists via infinite */|)
- Bayes chain rule
- Conditioning

### Would Need + For

- Marginalization: P(A) = sum_b P(A,b)
- This is probability-specific, not needed for FOL
- See Future Extension: ProbTT

## Relationship to Existing Systems

### vs Graded Type Theory (Granule/Gerty)

| Aspect | Graded types | CredTT |
|--------|--------------|--------|
| Structure | Semiring (needs +) | De Morgan (just * and ~) |
| Framing | MLTT + grades | Grades -> MLTT |
| Interpretation | Resource usage | Probability/confidence |

### vs MLTT

CredTT is MLTT with credences. MLTT is CredTT restricted to C = {0,1}.

## Prior Art and Literature Context

### What Already Exists

**1. Pavelka-style Fuzzy Logic (Graded Provability)**

Pavelka (1979) and Hajek (1998) developed logics where provability has degrees:
- Degree of provability: `|phi|_T = sup{r | T |- (phi, r)}`
- "True = provable to any degree below 1" is standard
- CredTT's `Gamma |- A @ c` is very close to Pavelka's graded formulas `(phi, r)`

Key reference: Hajek, *Metamathematics of Fuzzy Logic* (1998)

**2. Self-Reference Fixed Points (c = ~c -> c = 1/2)**

The liar paradox in fuzzy logic yields fixed points at intermediate values:
- Hajek, Paris, Shepherdson, "The Liar Paradox and Fuzzy Logic" (JSL 2000)
- Shows how 1/2 arises as stable value under self-referential evaluation
- CredTT's Godel fixed point is in this tradition

**3. Logics of Formal Inconsistency (LFIs)**

da Costa's C-systems and LFIs have object-level consistency operators:
- `@A` means "A is consistent"
- "Gentle explosion": from A, ~A, and @A derive anything
- Without @A, contradiction doesn't explode
- CredTT gates explosion by credence instead of a special connective

**4. Paraconsistent Fuzzy Logics**

Recent work (2024-2026) on degree-preserving Godel logics with involutive negation:
- Graded non-explosion
- Careful study of negation/explosion behavior
- Close to CredTT's "graded ex falso"

### What's New in CredTT

The existing literature provides:
- Graded provability degrees
- Self-reference fixed points at 1/2
- Graded consistency notions
- Non-explosive contradiction handling

CredTT's **novel contributions**:

1. **Dependent type theory packaging**: Pi/Sigma/Id interact with credences as first-class structure
2. **Credences primitive, MLTT as limit**: Not "MLTT + grades" but "grades -> MLTT"
3. **Conditioning replaces implication**: No residuated implication, just multiplicative chain rule
4. **De Morgan algebra, not t-norm**: Minimal structure (just * and ~, no +)

### Key Citations

| Topic | Primary Reference |
|-------|-------------------|
| Graded provability | Hajek 1998, Pavelka 1979 |
| Self-reference/liar | Hajek-Paris-Shepherdson 2000 |
| LFIs/paraconsistency | da Costa 1974, Carnielli-Coniglio 2016 |
| Degree-preserving logics | Recent work 2024-2026 |
| Graded type theory | Orchard et al. (Granule) |

### Positioning Summary

```
Fuzzy Logic (Pavelka/Hajek)     CredTT             Graded Types (Granule)
         |                         |                        |
   Graded provability         Credences as           Resource-tracking
   + truth degrees            foundation             on MLTT
         |                         |                        |
   Standard implication       Conditioning           Semiring grades
   (residuum)                 (multiplicative)       (needs +)
```

CredTT takes the graded provability insights from fuzzy logic and rebuilds dependent type theory from scratch, with conditioning (not implication) as the fundamental connective.

## Future Extension: ProbTT

ProbTT extends CredTT with addition (+) for marginalization:
- Marginalization: P(A) = sum_b P(A,b)
- Requires moving from De Morgan algebra to a semiring
- This is probability-specific, not needed for base logic

## File Structure

```
papers/
  credtt/
    credtt.tex    -- The specification (main document)
    credtt.pdf    -- Built paper
```

## Build

```bash
cd papers/credtt && pdflatex credtt.tex
```

## Current Status

Paper complete with:
- Credence algebra (minimal)
- All type formers (Pi, Sigma, +, Id)
- Markov structure (copy, delete)
- Chain rule (multiplicative Bayes)
- MLTT embedding theorem
- Graded ex falso

## Open Problems

1. **Implementation**: Type checker for CredTT
2. **Credence inference**: Can we infer credences from term structure?
3. **Continuous types**: Extension to measurable spaces
4. **Dependent credences**: c(x) varying over x in (x:A) -> B @ c(x)
