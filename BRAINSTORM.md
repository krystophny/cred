# Probabilistic Foundations: Probability as Primary, Logic as Derived

## Goal

**Replace logic with probability theory as the foundational system for mathematics.**

- Probability is primitive (the continuous [0,1] world)
- Logic is derived (the degenerate {0,1} boundary case)
- No set theory or measure theory as prerequisites
- Machine-verified from the ground up using a proof assistant

## Core Thesis

```
NOT:  Logic → Probability (probability extends logic)
BUT:  Probability → Logic (logic is degenerate probability)
```

Logic's "paradoxes" (LEM debates, Zorn's lemma, AC, Russell) may be artifacts of forcing continuous structure into discrete {0,1} boxes.

## Key Concepts

### Negation Spectrum

| Type | Definition | Character |
|------|------------|-----------|
| Weak negation | P(Aₙ) → 0 | Convergent implausibility |
| Strong negation | P(A) = 0 | Measure zero (set may be nonempty) |
| Classical negation | A → ⊥ | Degenerate {0,1} case |

Weak negation is the key insight: "A becomes arbitrarily implausible" without deciding A = ∅.

### Probabilistic Entailment

```
Γ ⊢ₚ φ  :=  E[φ | Γ] ≥ p
```

- Cut rule: P(ψ|Γ) ≥ P(ψ|φ)·P(φ|Γ)
- Weakening: Adding premises can only decrease probability
- Sequences of judgments and limits are first-class

### Borel-Cantelli as Proof Rule

If Σ P(Aₙ) < ∞ then P(Aₙ infinitely often) = 0.

Convergent weak negation → strong negation.

---

## Foundational Routes

### Route 1: Axiomatic Expectation

**Primitive**: Conditional expectation E[·|·] on [0,1]-valued functions

**Axioms**:
1. Linearity: E[af + bg | h] = aE[f|h] + bE[g|h]
2. Positivity: f ≥ 0 ⟹ E[f|h] ≥ 0
3. Normalization: E[1|h] = 1
4. Tower law: E[E[f|g]|h] = E[f|h] when h ≤ g
5. Product/Bayes: E[fg|h] relates to E[f|gh]·E[g|h]

**Derived**: Propositions are {0,1}-valued functions. Logic is the restriction.

**Pros**:
- Algebraically clean
- Direct path to probabilistic proof theory

**Cons**:
- Need to specify what "functions" are (requires some base structure)
- Tower law needs careful handling

**Proof assistant fit**: Agda/Lean with custom axioms

---

### Route 2: Markov Categories

**Primitive**: Category with
- Objects: "spaces"
- Morphisms X → Y: stochastic maps (not functions)
- Composition: Chapman-Kolmogorov

**Structure**:
- Copy/delete (Markov structure)
- Conditionals (Bayesian inversion as extra structure)
- Deterministic subcategory = ordinary functions = logic

**Hierarchy**:
```
Stochastic maps (probability)
       ↓ restrict to deterministic
Functions
       ↓ restrict to {0,1}-valued
Classical logic
```

**Pros**:
- Maximally synthetic (no sets, no measure theory)
- Composition is primitive (perfect for proof theory)
- Existing categorical semantics literature

**Cons**:
- Conditioning/disintegration is subtle
- Abstract; may be hard to compute with

**Proof assistant fit**:
- Agda with agda-categories
- Lean 4 with mathlib4 category theory
- Custom DSL on top

---

### Route 3: Probabilistic Programming Semantics

**Primitive**: Programs that sample from distributions

**Core**:
- Distribution monad / sampling semantics
- Conditioning via observe/score
- Expectation as program semantics

**Hierarchy**:
```
Probabilistic programs
       ↓ restrict to deterministic
Pure functions
       ↓ restrict to Bool-valued
Logical propositions
```

**Pros**:
- Extremely constructive
- Implementations exist (Church, Anglican, Pyro, Gen)
- Proof = program transformation

**Cons**:
- General conditioning needs care
- More "CS probability" than "foundations of math"

**Proof assistant fit**:
- Could build on Lean/Agda with monadic semantics
- Or: custom probabilistic proof assistant

---

### Route 4: De Finetti Coherence

**Primitive**: Betting prices that avoid sure loss (Dutch book)

**Axioms**: Coherence constraints on price assignments

**Derived**: Probability rules follow from no-arbitrage

**Pros**:
- Operational/decision-theoretic semantics
- Very philosophically grounded
- Minimal assumptions

**Cons**:
- Gets you finite additivity; countable additivity needs extra
- Less directly "proof-theoretic"

**Proof assistant fit**: Could axiomatize in any prover

---

### Route 5: Custom Proof Assistant

**Idea**: Build a proof assistant where probability is primitive

**Core features**:
- Judgments are probabilistic: Γ ⊢ₚ φ (entailment with confidence p)
- Proof terms carry probability bounds
- Cut rule is probabilistic composition
- Limits/convergence built into the type system

**Possible base**:
- Fork Lean 4 / Agda and modify kernel
- Or: build from scratch in Rust/OCaml
- Or: DSL that compiles to existing prover

**Pros**:
- Exactly fits the vision
- No fighting existing foundations

**Cons**:
- Significant engineering effort
- Ecosystem from scratch

---

## Proof Assistant Options

### Option A: Agda with Postulates

- Postulate probabilistic axioms
- Build theory on top
- Use --safe where possible, document postulates

**Effort**: Low
**Risk**: Postulates might be inconsistent

### Option B: Lean 4 with Custom Axioms

- Use Lean's axiom mechanism
- Build Mathlib-independent foundation
- Good tooling, active community

**Effort**: Medium
**Risk**: May fight Mathlib conventions

### Option C: Coq with Custom Logic

- Coq allows alternative logics
- Could define probabilistic logic as alternate foundation
- Mature ecosystem

**Effort**: Medium
**Risk**: Coq's classical bias may interfere

### Option D: Build Custom Prover

- Full control over foundations
- Probability primitive from day one
- Could target novel applications (AI, statistical inference)

**Effort**: High (6+ months for minimal viable)
**Risk**: Maintenance burden, adoption

### Option E: Hybrid - DSL + Backend

- DSL for probabilistic proofs
- Compiles to Agda/Lean/Coq for verification
- Best of both worlds?

**Effort**: Medium-High
**Risk**: Translation correctness

---

## Key Questions to Decide

### Q1: What is the primitive?

- [ ] Expectation E[·|·]
- [ ] Stochastic maps (Markov categories)
- [ ] Sampling programs
- [ ] Betting prices
- [ ] Something else?

### Q2: What proof assistant?

- [ ] Agda (familiar from metalogics project)
- [ ] Lean 4 (better tooling, growing community)
- [ ] Coq (mature, but classical bias)
- [ ] Custom (full control, high effort)
- [ ] Hybrid DSL

### Q3: How to handle convergence/limits?

- [ ] Axiomatize ε-δ style
- [ ] Use coinduction/codata
- [ ] Build into judgment form
- [ ] Defer (handle discrete case first)

### Q4: Target applications?

- [ ] Pure foundations (replace ZFC-style set theory)
- [ ] Probabilistic programming semantics
- [ ] Statistical inference / Bayesian reasoning
- [ ] AI/ML foundations
- [ ] All of the above

### Q5: Scope of first paper?

- [ ] Minimal: axioms + basic derived rules + one example
- [ ] Medium: full proof theory + logic-as-special-case theorem
- [ ] Ambitious: probabilistic set theory + Zorn analog

---

## Comparison with Existing Work

### QBS (Quasi-Borel Spaces)
- Synthetic measure theory in type theory
- Still starts from "spaces" and adds probability
- We want probability more primitive

### Probabilistic Programming Languages
- Church, Anglican, Pyro, Gen, etc.
- Focus on inference algorithms, not foundations
- Could inform our semantics

### Markov Categories Literature
- Fritz, Cho, Jacobs, etc.
- Categorical probability without measure theory
- Strong candidate for our foundation

### HoTT/Univalent Foundations
- Not needed for core thesis
- Could be one target for "proofs as programs"
- Orthogonal concern

---

## Immediate Next Steps

1. **Choose proof assistant** (or decide to build custom)
2. **Write minimal axiom system** for probabilistic entailment
3. **Prove basic metatheorems** (cut, weakening, etc.)
4. **Show logic embeds** as {0,1} special case
5. **Pick one "hard example"** (Zorn? AC? LEM?) and see if probabilistic treatment helps

---

## References to Study

- Cox, R.T. (1946). Probability, Frequency and Reasonable Expectation
- Jaynes, E.T. (2003). Probability Theory: The Logic of Science
- Fritz, T. (2020). A synthetic approach to Markov kernels
- Cho & Jacobs (2019). Disintegration and Bayesian inversion via string diagrams
- Ścibior et al. (2018). Functional programming for modular Bayesian inference
- Heunen, Kammar, et al. (2017). A convenient category for higher-order probability theory
- de Finetti (1937). Foresight: Its Logical Laws, Its Subjective Sources

---

## Notes / Scratchpad

(Add ongoing thoughts here)

### On Zorn's Lemma

Classical: Every chain-complete poset has a maximal element.

Probabilistic version?: Every chain-complete poset admits a distribution concentrated on "near-maximal" elements, where "near-maximal" means "probability of finding a strictly greater element → 0".

This avoids picking a specific maximum while still giving useful existence.

### On Excluded Middle

Classical: P ∨ ¬P (must decide)
Probabilistic: P(A) + P(¬A) = 1 (algebraic identity, no decision)

The "decision" is replaced by a constraint. You can work with both possibilities weighted by their probabilities.

### On Constructivism vs Classical

The debate is about whether ¬¬A → A.

Probabilistically: P(A) > 0 does not imply P(A) = 1.

The debate dissolves because we're not in {0,1}. We have a spectrum.
