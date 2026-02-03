# Cred: A Credence Algebra for Graded Mathematics

## What is Credence?

**Credence** is the term used in formal epistemology and Bayesian philosophy for **degree of belief**—a real number in [0,1] representing how confident a rational agent is in a proposition.

If you know probability theory, credence is essentially **subjective probability** (in the sense of de Finetti, Ramsey, Savage, and Jaynes), but with important differences in how we handle edge cases.

### Credence vs. Probability: For Probability Theorists

| Aspect | Standard Probability | Credence (Cred) |
|--------|---------------------|-----------------|
| **Interpretation** | Frequentist, propensity, or subjective | Explicitly epistemic (degree of belief) |
| **Conditioning at 0** | P(A\|B) undefined when P(B)=0 | cred(A\|B) unconstrained when cred(B)=0 |
| **Ex falso** | Not applicable (undefined) | Blocked (no forced value) |
| **Chain rule** | Derived: P(A\|B) = P(A∧B)/P(B) | **Primitive axiom**: cred(A\|B)·cred(B) = cred(A∧B) |
| **Boolean collapse** | Classical logic (has ex falso) | Relevant logic (no ex falso) |

### Why "Credence" Instead of "Probability"?

1. **Terminological clarity**: "Credence" is unambiguous—it always means degree of belief. "Probability" is overloaded (frequentist, propensity, subjective, logical).

2. **Different edge-case behavior**: When evidence has measure zero, probability theory says conditioning is *undefined*. Cred says it's *unconstrained*—any value satisfies the chain rule. This blocks ex falso quodlibet.

3. **Alignment with formal epistemology**: The term is standard in philosophy (see [Stanford Encyclopedia](https://plato.stanford.edu/entries/epistemology-bayesian/), Pettigrew's *Accuracy and the Laws of Credence*, Easwaran's work on probabilism).

4. **Historical precedent**: Keynes, Ramsey, de Finetti, and Carnap all worked with "degrees of belief" as the primitive notion. We follow this tradition with modern formalization.

### The "Conditional First" Principle

A key philosophical stance: **conditioning is more fundamental than absolute assignment.**

This parallels a crucial lesson from set theory:

> In naive set theory, unrestricted comprehension ("the set of all x such that φ(x)") leads to Russell's paradox. The solution: there are only **subsets of sets**, not "the subset of everything." Absolute, unrestricted set formation is replaced by relative, conditional set formation.

The same principle applies to probability:

> Rényi (1955) and Popper (1959) argued that **conditional probability is more fundamental than absolute probability**. Instead of defining P(A|B) = P(A∧B)/P(B) (which fails when P(B)=0), we take conditioning as primitive and derive absolute probability as the special case P(A) = P(A|Ω).

| Domain | Problematic "Absolute" | Safe "Conditional" |
|--------|------------------------|-------------------|
| **Set theory** | Unrestricted comprehension → Russell's paradox | Only subsets of existing sets |
| **Probability** | P(A\|B) = P(A∧B)/P(B) → undefined at 0 | Chain rule as primitive axiom |
| **Logic** | Ex falso quodlibet (⊥ → A) | No ex falso (conditioning unconstrained) |

Cred adopts this "conditional first" philosophy throughout.

### Key Literature on Credence

- **Ramsey (1926)**: "Truth and Probability" — foundational work on degrees of belief
- **de Finetti (1937)**: "La prévision" — coherence, exchangeability, subjective probability
- **Savage (1954)**: *Foundations of Statistics* — decision-theoretic foundation
- **Jaynes (2003)**: *Probability Theory: The Logic of Science* — probability as extended logic
- **Pettigrew (2016)**: *Accuracy and the Laws of Credence* — accuracy-based epistemology
- **Easwaran (2011)**: "Bayesianism" (survey in *Philosophy Compass*)

## Philosophy: Inference as Constraint

**Inference narrows possibilities from uncertainty, not builds certainties from nothing.**

In the Bayesian view (Jaynes, de Finetti, Cox):
- **Prior**: Maximal uncertainty—flat distribution over possibilities
- **Evidence constrains**: Narrows the space of consistent beliefs
- **Posterior**: Prior + constraints
- **No evidence = no constraint**: Credence 0 evidence provides nothing to constrain with

This explains Cred's key design choices:
- **Conditioning is primitive**: Inference IS constraining belief by evidence
- **No ex falso**: Impossible evidence provides no constraint (not "everything follows")
- **0.5 = maximal uncertainty**: Flat prior over {true, false}
- **Chain rule is fundamental**: cred(A|B)·cred(B) = cred(A∧B) expresses constraint propagation

## The Cred Algebra

Credences are values in [0,1] with operations:

| Operation | Definition | Meaning |
|-----------|------------|---------|
| **Negation** | ~c = 1 - c | Complement of belief |
| **Conjunction** | c₁ ⊗ c₂ = c₁·c₂ | Joint belief (independence assumed) |
| **Disjunction** | c₁ ⊔ c₂ = c₁ + c₂ - c₁·c₂ | De Morgan dual |
| **Conditioning** | cred(A\|B)·cred(B) = cred(A∧B) | Chain rule (primitive) |

**Key property**: When cred(B) = 0, the chain rule becomes cred(A|B)·0 = 0, satisfied by ANY value. Conditioning is unconstrained, not undefined.

## Why Graded?

| Binary Logic | Cred |
|--------------|------|
| Undecidable = stuck, no value | Undecidable = credence 0.5 |
| Paradoxes break the system | Paradoxes → fixed points |
| Ex falso: nonsense follows | No ex falso: relevance preserved |

## Collapse Hierarchy

When we collapse to binary, we land in **relevant logic**, not classical:

```
Cred [0,1]          graded (where we work)
    ↓ collapse
{0, ½, 1}           three-valued relevant (RM3-like)
    ↓ collapse
{0, 1}              Boolean relevant logic (R, E)
    ↓ + ex falso
Classical FOL       (requires extra axiom)
```

**Key insight**: Cred generalizes **relevant logic** (no ex falso). Fuzzy logic generalizes **classical logic** (has ex falso). These are fundamentally different.

## Fixed Points and Self-Reference

The liar sentence L = "This sentence is false" satisfies L ≡ ¬L.

In Cred: cred(L) = ~cred(L) = 1 - cred(L), so cred(L) = 0.5.

Self-reference produces a **fixed point** (meaningful value), not a paradox.

## Structure

- **lean/**: Lean 4 formalization (machine-checked proofs)
- **part1/**: Primitives, collapse hierarchy, publication paper
- **part2/**: Graded mathematics
- **part3/**: Self-hosting and undecidability

## Prior Art

| Source | Contribution | Our use |
|--------|--------------|---------|
| **Ramsey (1926)** | Degrees of belief, Dutch book | Foundational |
| **de Finetti (1937)** | Coherence, exchangeability | Constraint consistency |
| **Jaynes (1957, 2003)** | Maximum entropy, probability as logic | Inference as constraint |
| **Shore & Johnson (1980)** | Uniqueness of entropy for constraints | Theoretical foundation |
| **Rényi (1955)** | Conditional probability as primitive | Chain rule axiom |
| **Popper (1959)** | Primitive conditional probability | Alternative to division |
| **van Fraassen (1983)** | Probabilistic semantics for relevant logic | Semantic correspondence |
| **Anderson & Belnap (1975)** | Relevant logic (no ex falso) | Boolean collapse target |
| **Walley (1991)** | Imprecise probability, credal sets | Constraint regions |
| **Fritz (2020)** | Markov categories | Conditioning without division |
