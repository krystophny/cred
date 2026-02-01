# Proof Assistant Requirements

## Core Requirement

**Every claim must be machine-verified from the start.**

We don't want to write informal math and formalize later. The proof assistant is the medium of thought.

## What We Need

### 1. Probabilistic Judgments as Primitive

Standard proof assistants have:
```
Γ ⊢ φ    (context entails proposition)
```

We need:
```
Γ ⊢ₚ φ   (context entails proposition with probability ≥ p)
```

Or equivalently:
```
E[φ | Γ] ≥ p
```

### 2. Proof Terms Carry Bounds

A proof term `t : Γ ⊢ₚ φ` should:
- Witness that the bound p is achieved
- Compose: if `t₁ : Γ ⊢ₚ φ` and `t₂ : φ ⊢_q ψ` then `t₁;t₂ : Γ ⊢_{p·q} ψ`
- Support weakening, exchange (with appropriate bound adjustments)

### 3. Limits/Convergence

For weak negation (P(Aₙ) → 0), we need:
- Sequences of judgments
- Limit judgments
- Borel-Cantelli as a derived rule

### 4. {0,1} Specialization

When all probabilities are 0 or 1, we should recover classical logic automatically.

This means: classical logic proofs are valid probabilistic proofs (with p=1).

---

## Evaluation of Existing Proof Assistants

### Agda

**Strengths**:
- Dependent types
- Excellent for defining custom logics
- We used it for metalogics project
- Cubical Agda for HoTT if needed

**Weaknesses**:
- No built-in reals (need postulates or heavy encoding)
- Would need to axiomatize probability

**Approach**:
```agda
postulate
  Prob : Set
  _≤_ : Prob → Prob → Set
  E[_|_] : (A → Prob) → (A → Prob) → Prob
  -- axioms...

data _⊢_≥_ (Γ : Context) (φ : Prop) (p : Prob) : Set where
  -- inference rules as constructors
```

**Verdict**: Viable. Medium effort. May feel like "fighting the system."

---

### Lean 4

**Strengths**:
- Modern, fast, good tooling
- Metaprogramming via macros
- Active community
- Could build custom tactics for probabilistic reasoning

**Weaknesses**:
- Mathlib assumes classical logic + ZFC-style foundations
- Would need to work outside Mathlib or carefully extend

**Approach**:
```lean
axiom Prob : Type
axiom prob_le : Prob → Prob → Prop
axiom cond_exp : (α → Prob) → (α → Prob) → Prob

structure ProbJudgment (Γ : Context) (φ : Prop) (p : Prob) where
  witness : -- proof that E[φ|Γ] ≥ p
```

**Verdict**: Viable. Good tooling. Community support. May be best choice.

---

### Coq

**Strengths**:
- Mature, well-understood
- Allows custom logics (Program, Equations, etc.)
- Good extraction to OCaml

**Weaknesses**:
- Heavier than Lean/Agda
- Classical bias in standard library
- Less active development

**Verdict**: Viable but not preferred.

---

### Custom Proof Assistant

**What it would look like**:
- Core type theory with probabilistic judgments built in
- Prob as a built-in type (like Nat in most provers)
- Inference rules for probabilistic entailment in the kernel
- Tactics for bound computation

**Implementation options**:
1. **Fork Lean 4**: Modify kernel to add Prob type and probabilistic judgment form
2. **Build from scratch**: Rust/OCaml, bidirectional type checking
3. **Shallow embedding**: DSL that compiles to Lean/Agda

**Minimum viable features**:
- Dependent types (for indexing by probability bounds)
- Probabilistic judgment form Γ ⊢ₚ φ
- Basic inference rules (axiom, cut, weakening)
- Real number type with ordering
- Tactics: `bound_check`, `compose`, `specialize_to_classical`

**Effort estimate**:
- Minimal kernel: 2-3 months
- Usable system: 6+ months
- With tactics and UI: 1 year+

**Verdict**: High effort but perfect fit. Consider hybrid approach first.

---

## Recommended Path

### Phase 1: Prototype in Lean 4 (1-2 months)

1. Define `Prob` type (axiomatically or as `ℝ≥0≤1`)
2. Define probabilistic judgment structure
3. Prove basic metatheorems (cut, weakening)
4. Show classical logic embeds
5. Test on one hard example

**Goal**: Validate the approach before committing to custom prover.

### Phase 2: Evaluate (1 month)

- Is Lean 4 sufficient?
- What's painful? What's missing?
- Do we need custom kernel features?

### Phase 3: Decide

- If Lean 4 works: continue building there
- If limited: design custom prover based on learnings
- If hybrid: build DSL that generates Lean 4

---

## Initial Lean 4 Experiment

```lean
-- Probability bound type
abbrev Prob := { x : Float // 0 ≤ x ∧ x ≤ 1 }

-- Probabilistic entailment (simplified)
structure ProbEntails (Γ : List Prop) (φ : Prop) (p : Prob) : Prop where
  bound : -- E[φ|Γ] ≥ p

-- Classical logic as special case
def classical_entails (Γ : List Prop) (φ : Prop) : Prop :=
  ProbEntails Γ φ ⟨1.0, by norm_num, by norm_num⟩

-- Cut rule (probabilistic)
theorem prob_cut {Γ : List Prop} {φ ψ : Prop} {p q : Prob} :
  ProbEntails Γ φ p → ProbEntails [φ] ψ q → ProbEntails Γ ψ (p * q) := by
  sorry -- to be proved
```

This is rough but shows the shape.

---

## Questions for Phase 1

1. Use Float or Real? (Float is computable, Real is exact)
2. How to handle conditioning? (Requires non-zero denominator)
3. Axiomatize or construct Prob? (Axioms faster, construction safer)
4. What's our first "theorem"? (Suggest: probabilistic cut rule)
