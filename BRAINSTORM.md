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

---

## CRITICAL: Meta-Level vs Object-Level Separation

### The Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│  METALOGIC: Lean's Type Theory                                  │
│  (Used ONLY to define and verify the probabilistic system)      │
│  - Dependent types, inductive types, tactics                    │
│  - This is our SPECIFICATION LANGUAGE                           │
│  - Classical/intuitionistic - doesn't matter, it's scaffolding  │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ defines, reasons about
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  OBJECT SYSTEM: Probabilistic Foundations                       │
│  (Where actual mathematics happens)                             │
│  - Probability is primitive                                     │
│  - NO logical connectives except as derived {0,1} cases         │
│  - This is what REPLACES classical logic for doing math         │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ contains as degenerate case
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│  CLASSICAL LOGIC: The {0,1} Boundary                            │
│  (What we currently use - now just a special case)              │
└─────────────────────────────────────────────────────────────────┘
```

### ⚠️ DANGER: Logic Slippage ⚠️

**THE CRITICAL DISCIPLINE**: Lean's logical connectives (∧, ∨, →, ¬, ∀, ∃) must NEVER appear at the object level except when explicitly deriving them as the {0,1} special case.

**BAD** (logic slipping into object level):
```lean
-- WRONG: Using Lean's ∧ in probabilistic theorem
theorem bad_example : P(A) > 0 ∧ P(B) > 0 → P(A ∩ B) > 0 := ...
```

**GOOD** (clean separation):
```lean
-- RIGHT: Everything probabilistic at object level
theorem good_example : prob_positive A → prob_positive B →
                       prob_positive (prob_intersect A B) := ...

-- Where prob_positive, prob_intersect are OUR primitives,
-- not Lean's logical connectives
```

**Rules to enforce**:

1. **Object-level theorems use ONLY**:
   - `Prob` type and its operations (+, *, ≤)
   - `𝔼[·|·]` conditional expectation
   - `⊢[p]` probabilistic entailment
   - Derived notions built from these

2. **Lean's logic is ONLY for**:
   - Defining what the probabilistic primitives ARE
   - Stating metatheorems ABOUT the probabilistic system
   - Proof automation internals

3. **Test for slippage**: If you can state a theorem using Lean's Prop, you're probably doing it wrong. Object-level statements should be about `Prob` values.

### Why This Matters

If we accidentally use logical reasoning at the object level:
- We haven't replaced logic, we've just added probability on top
- The whole project becomes pointless
- We inherit all the "paradoxes" we're trying to avoid

The analogy: ZFC defines sets using first-order logic, then does mathematics IN sets without constantly invoking the metalogic. We define probability using type theory, then do mathematics IN probability.

### Self-Hosting (Future)

Eventually, a truly probabilistic proof assistant would have:
- Probabilistic judgments at the KERNEL level
- Type checking with confidence bounds
- No classical/intuitionistic metalogic at all

But that's a much harder problem. For now: clean separation is the discipline.

---

## Why Lean 4 (Not Agda)

### Lean is the Better Choice

| Aspect | Lean 4 | Agda |
|--------|--------|------|
| **Tooling** | Excellent (LSP, widgets, profiler) | Good but dated |
| **Community** | Large, growing (Mathlib) | Smaller, academic |
| **Industry** | Used at AWS, Microsoft | Mostly academic |
| **Metaprogramming** | First-class (macros, tactics) | Limited |
| **Performance** | Compiled, fast | Interpreted, slower |
| **Documentation** | Extensive, improving | Sparse |
| **Future** | Active development | Maintenance mode |

### Lean-Specific Advantages for This Project

1. **Custom tactics**: We can write tactics for probabilistic bound propagation
2. **Axiom mechanism**: Clean way to postulate our primitives
3. **Notation**: Flexible syntax for `𝔼[·|·]` and `⊢[p]`
4. **Separation from Mathlib**: Can build independent foundation without importing classical math
5. **Lake build system**: Easy project management

### Migration Path

Our Agda prototype (`agda/Foundations.agda`) translates directly to Lean:
- `postulate` → `axiom`
- `record` → `structure`
- Syntax is similar enough

**Decision: Use Lean 4 as the primary proof assistant.**

---

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

### ✅ CHOSEN: Lean 4 with Custom Axioms

- Use Lean's axiom mechanism for probabilistic primitives
- Build Mathlib-INDEPENDENT foundation (avoid importing classical logic)
- Excellent tooling, active community, industry adoption
- Custom tactics for probabilistic reasoning

**Effort**: Medium
**Risk**: Must be vigilant about logic slippage from Lean's Prop

### Option B: Agda with Postulates (BACKUP)

- Postulate probabilistic axioms
- Familiar from metalogics project
- Use --safe where possible, document postulates

**Effort**: Low
**Risk**: Postulates might be inconsistent; weaker tooling

### Option C: Coq with Custom Logic (NOT RECOMMENDED)

- Coq allows alternative logics
- But: classical bias in ecosystem, declining community

**Effort**: Medium
**Risk**: Fighting the system

### Option D: Build Custom Prover (FUTURE)

- Full control over foundations
- Probability primitive at kernel level
- The "self-hosting" vision

**Effort**: High (6+ months for minimal viable)
**Risk**: Only pursue after Lean prototype validates the approach

### Option E: Hybrid DSL (MAYBE LATER)

- DSL for probabilistic proofs with nicer syntax
- Compiles to Lean 4 for verification
- Consider after core theory is stable

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
- [x] **Lean 4** (better tooling, growing community) ← CHOSEN
- [ ] Coq (mature, but classical bias)
- [ ] Custom (full control, high effort) ← future self-hosting goal
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

## Gap Analysis: What Exists vs What We Build

### What EXISTS (we can build upon)

| Resource | Description | How We Use It |
|----------|-------------|---------------|
| [Mathlib.CategoryTheory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html) | Category theory in Lean 4 | Base for Markov category structure |
| [Fritz 2020 - Markov Categories](http://tobiasfritz.science/2020/markov_cats.pdf) | Theoretical foundations | Our mathematical blueprint |
| [nLab - Markov category](https://ncatlab.org/nlab/show/Markov+category) | Definitions & references | Formalization target |
| [Cho & Jacobs 2019](https://arxiv.org/abs/1709.00322) | String diagrams for Bayes | Conditioning/disintegration |
| [jwiegley/category-theory](https://github.com/jwiegley/category-theory) | Category theory in Coq | Reference patterns |
| [Audebaud & Paulin 2006](https://link.springer.com/chapter/10.1007/11783596_6) | Monadic probability in Coq | Probabilistic monad patterns |
| [Brownian motion in Lean](https://arxiv.org/abs/2511.20118) | Measure-theoretic, but shows Lean handles probability | Proof patterns |

### What DOESN'T exist (our novel contributions)

| Gap | Status | Our Contribution |
|-----|--------|------------------|
| Markov categories in proof assistant | **NOT FORMALIZED** | First formalization |
| Synthetic probability (non-measure-theoretic) | **DOESN'T EXIST** | New approach |
| Probability-as-foundation | **NOBODY HAS TRIED** | Main thesis |
| Logic derived from probability | **NOVEL** | Philosophical payoff |
| Weak negation (P→0) formalized | **NOVEL** | New logical concept |

### Our Build Strategy

```
┌─────────────────────────────────────────────────────────────────┐
│  LAYER 0: Mathlib.CategoryTheory (existing)                     │
│  - Monoidal categories, functors, natural transformations       │
└─────────────────────────────────────────────────────────────────┘
                              ↑ import selectively
┌─────────────────────────────────────────────────────────────────┐
│  LAYER 1: Markov Categories (WE BUILD - first formalization)    │
│  - Copy-delete structure                                        │
│  - Stochastic morphisms                                         │
│  - Conditionals / Bayesian inversion                            │
└─────────────────────────────────────────────────────────────────┘
                              ↑ build on top
┌─────────────────────────────────────────────────────────────────┐
│  LAYER 2: Probabilistic Foundations (WE BUILD - main thesis)    │
│  - Prob type, conditional expectation                           │
│  - Probabilistic entailment ⊢[p]                                │
│  - Proof rules (cut, weakening, etc.)                           │
└─────────────────────────────────────────────────────────────────┘
                              ↑ derive as special case
┌─────────────────────────────────────────────────────────────────┐
│  LAYER 3: Classical Logic (derived {0,1} case)                  │
│  - Show standard logic embeds                                   │
│  - LEM as algebraic identity                                    │
└─────────────────────────────────────────────────────────────────┘
```

---

## Concrete Execution Plan

### Phase 1: Lean 4 Setup & Markov Categories (Weeks 1-4)

**Goal**: First-ever formalization of Markov categories in a proof assistant.

**Tasks**:
1. Create Lean 4 project with Lake, minimal Mathlib imports (CategoryTheory only)
2. Define `MarkovCategory` structure:
   ```lean
   class MarkovCategory (C : Type*) extends Category C, MonoidalCategory C where
     copy : ∀ X, X ⟶ X ⊗ X
     delete : ∀ X, X ⟶ 𝟙_ C
     -- coherence axioms
   ```
3. Define stochastic morphisms, composition (Chapman-Kolmogorov)
4. Prove basic lemmas (associativity, unitality)

**Deliverable**: `Mathlib/CategoryTheory/Markov/Basic.lean`

**References to follow**:
- [Fritz 2020 Section 2-3](http://tobiasfritz.science/2020/markov_cats.pdf)
- [nLab Markov category](https://ncatlab.org/nlab/show/Markov+category)

---

### Phase 2: Probabilistic Primitives (Weeks 5-8)

**Goal**: Axiomatize probability without measure theory.

**Tasks**:
1. Define `Prob` type (unit interval with operations)
2. Define conditional expectation `𝔼[_|_]` axiomatically:
   ```lean
   axiom CondExp {α : Type*} : ProbProp α → ProbProp α → Prob
   notation "𝔼[" f " | " g "]" => CondExp f g

   axiom condexp_norm : 𝔼[ 1 | g ] = 1
   axiom condexp_mono : (∀ x, f x ≤ f' x) → 𝔼[f|g] ≤ 𝔼[f'|g]
   axiom condexp_product : 𝔼[f * g | h] = 𝔼[f | g * h] * 𝔼[g | h]  -- Bayes
   ```
3. Define probabilistic entailment:
   ```lean
   structure ProbEntails (Γ φ : ProbProp α) (p : Prob) : Type where
     bound : p ≤ 𝔼[φ | Γ]
   notation Γ " ⊢[" p "] " φ => ProbEntails Γ φ p
   ```

**Deliverable**: `Foundations/Probability/Basic.lean`

---

### Phase 3: Proof Theory (Weeks 9-12)

**Goal**: Derive proof rules, show they work.

**Tasks**:
1. Prove cut rule:
   ```lean
   theorem cut : (Γ ⊢[p] φ) → (φ ⊢[q] ψ) → (Γ ⊢[p * q] ψ)
   ```
2. Prove weakening (with probability adjustment)
3. Prove exchange
4. Define weak negation (sequences with P → 0)
5. State and prove Borel-Cantelli as derived rule

**Deliverable**: `Foundations/Probability/ProofTheory.lean`

---

### Phase 4: Logic as Special Case (Weeks 13-16)

**Goal**: Show classical logic embeds as {0,1} restriction.

**Tasks**:
1. Define `ClassicalProp` as `{f : ProbProp α // ∀ x, f x = 0 ∨ f x = 1}`
2. Show classical entailment = probabilistic entailment with p = 1
3. Derive ∧, ∨, → as special cases of probabilistic operations
4. Show LEM is the algebraic identity P(A) + P(¬A) = 1
5. Show constructive/classical debate dissolves in probabilistic setting

**Deliverable**: `Foundations/Classical/Embedding.lean`

---

### Phase 5: Hard Example - Probabilistic Choice (Weeks 17-20)

**Goal**: Show probabilistic foundations handle AC-like situations differently.

**Tasks**:
1. State probabilistic Zorn: "distributions concentrated on near-maximal elements"
2. Formalize "near-maximal": P(finding strictly greater) → 0
3. Compare with classical AC
4. Document what changes, what's gained

**Deliverable**: `Foundations/Examples/Choice.lean` + paper section

---

### Phase 6: Paper & Documentation (Weeks 21-24)

**Goal**: Publishable paper with all claims machine-verified.

**Structure**:
1. Introduction: Logic's limitations, probability as alternative
2. Background: Markov categories (with citations)
3. Formalization: Our Lean development
4. Main results: Proof theory + logic embedding
5. Philosophy: LEM, AC, constructivism reinterpreted
6. Conclusion: What this enables

**Target venue**: Journal of Philosophical Logic, or Logical Methods in Computer Science

---

## References (with URLs)

### Core Mathematical Foundations

1. **Fritz, T. (2020)**. A synthetic approach to Markov kernels, conditional independence and theorems on sufficient statistics.
   - PDF: http://tobiasfritz.science/2020/markov_cats.pdf
   - arXiv: https://arxiv.org/abs/1908.07021
   - **Key for**: Markov category definitions, axioms

2. **Cho, K. & Jacobs, B. (2019)**. Disintegration and Bayesian inversion via string diagrams.
   - arXiv: https://arxiv.org/abs/1709.00322
   - **Key for**: Conditioning, Bayesian inversion structure

3. **Fritz, T. et al. (2023)**. Representable Markov categories and comparison of statistical experiments.
   - DOI: https://doi.org/10.1016/j.tcs.2023.114063
   - **Key for**: Advanced Markov category theory

4. **nLab**. Markov category.
   - https://ncatlab.org/nlab/show/Markov+category
   - **Key for**: Quick reference, bibliography

### Philosophical Foundations

5. **Cox, R.T. (1946)**. Probability, Frequency and Reasonable Expectation.
   - DOI: https://doi.org/10.1119/1.1990764
   - **Key for**: Probability from plausibility axioms

6. **Jaynes, E.T. (2003)**. Probability Theory: The Logic of Science.
   - Cambridge University Press
   - **Key for**: "Probability as extended logic" philosophy

7. **de Finetti, B. (1937)**. Foresight: Its Logical Laws, Its Subjective Sources.
   - **Key for**: Coherence/Dutch book foundations

### Proof Assistant Resources

8. **Mathlib Category Theory**
   - Docs: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html
   - GitHub: https://github.com/leanprover-community/mathlib4
   - **Key for**: Our foundation layer

9. **Wiegley, J.** category-theory (Coq)
   - https://github.com/jwiegley/category-theory
   - **Key for**: Patterns, reference

10. **Audebaud & Paulin-Mohring (2006)**. Proofs of randomized algorithms in Coq.
    - https://link.springer.com/chapter/10.1007/11783596_6
    - **Key for**: Monadic probability patterns

### Recent Formalizations

11. **Gouëzel, S. (2025)**. Formalization of Brownian motion in Lean.
    - https://arxiv.org/abs/2511.20118
    - **Key for**: Shows Lean handles probability

12. **Tan et al. (2025)**. Towards Formalizing Reinforcement Learning Theory.
    - https://arxiv.org/abs/2511.03618
    - **Key for**: Conditional expectation in Lean patterns

### Categorical Probability (Further Reading)

13. **Patterson, E.** Categorical probability theory (wiki).
    - https://www.epatters.org/wiki/stats-ml/categorical-probability-theory
    - **Key for**: Overview, more references

14. **Introduction to Categorical Probability** (n-Category Café, 2024)
    - https://golem.ph.utexas.edu/category/2024/08/introduction_to_categorical_pr.html
    - **Key for**: Accessible introduction

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

---

## Checklist: Avoiding Logic Slippage

Before any theorem/definition, ask:

1. **Does this use Lean's Prop?** If yes → probably wrong
2. **Does this use ∧, ∨, →, ¬?** If yes → must be metatheorem only
3. **Could this be stated purely in terms of Prob and 𝔼?** If yes → do that
4. **Is this about the system or in the system?**
   - ABOUT = metatheorem, Lean logic OK
   - IN = object-level, only probabilistic primitives

### Examples of Correct Separation

**Metatheorem (ABOUT the system)** - Lean logic OK:
```lean
-- "If p ≤ q then the bound transfers" - statement ABOUT our system
theorem bound_mono : p ≤ q → (Γ ⊢[p] φ) → (Γ ⊢[q] φ) := ...
```

**Object-level theorem (IN the system)** - NO Lean logic:
```lean
-- "Probability of union bounded by sum" - theorem IN our system
theorem union_bound (A B : ProbProp α) :
  𝔼[ prob_or A B ∣ ctx ] ≤ₚ 𝔼[ A ∣ ctx ] +ₚ 𝔼[ B ∣ ctx ] := ...
```

Notice: second theorem uses only `≤ₚ`, `+ₚ`, `𝔼`, `prob_or` - all OUR primitives.

### Red Flags

Watch for these patterns that indicate slippage:

- `∀ x, P x → Q x` at object level (should be probabilistic implication)
- `∃ x, P x` at object level (should be `𝔼[ indicator_P ∣ ctx ] > 𝟘`)
- `A ∧ B` at object level (should be `prob_and A B`)
- `¬ A` at object level (should be `complement A` with `𝔼[A] +ₚ 𝔼[¬A] = 𝟙`)

The discipline is: **if it's not about Prob values, it shouldn't be at object level.**
