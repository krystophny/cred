/-
# Probabilistic Foundations

Probability as primitive, logic as derived.

This file explores axiomatizing probability theory directly,
without going through set theory or measure theory.
-/

-- We work with an abstract probability type in [0,1]
-- Later we can instantiate with reals

axiom Prob : Type
axiom Prob.zero : Prob
axiom Prob.one : Prob
axiom Prob.le : Prob → Prob → Prop
axiom Prob.add : Prob → Prob → Prob
axiom Prob.mul : Prob → Prob → Prob
axiom Prob.sub : Prob → Prob → Prob  -- truncated subtraction

notation "𝟘" => Prob.zero
notation "𝟙" => Prob.one
infix:50 " ≤ₚ " => Prob.le
infix:65 " +ₚ " => Prob.add
infix:70 " *ₚ " => Prob.mul
infix:65 " -ₚ " => Prob.sub

-- Basic axioms for probability bounds
axiom Prob.zero_le : ∀ p : Prob, 𝟘 ≤ₚ p
axiom Prob.le_one : ∀ p : Prob, p ≤ₚ 𝟙
axiom Prob.le_refl : ∀ p : Prob, p ≤ₚ p
axiom Prob.le_trans : ∀ p q r : Prob, p ≤ₚ q → q ≤ₚ r → p ≤ₚ r
axiom Prob.le_antisymm : ∀ p q : Prob, p ≤ₚ q → q ≤ₚ p → p = q

-- Multiplication preserves bounds
axiom Prob.mul_le_mul : ∀ p₁ p₂ q₁ q₂ : Prob,
  p₁ ≤ₚ q₁ → p₂ ≤ₚ q₂ → (p₁ *ₚ p₂) ≤ₚ (q₁ *ₚ q₂)

axiom Prob.one_mul : ∀ p : Prob, 𝟙 *ₚ p = p
axiom Prob.mul_one : ∀ p : Prob, p *ₚ 𝟙 = p
axiom Prob.mul_comm : ∀ p q : Prob, p *ₚ q = q *ₚ p
axiom Prob.mul_assoc : ∀ p q r : Prob, (p *ₚ q) *ₚ r = p *ₚ (q *ₚ r)

/-
## Probabilistic Propositions

A probabilistic proposition over a type α is a function α → Prob.
Think of α as a sample space and the function as assigning
probability mass (or density) to each point.
-/

def ProbProp (α : Type) := α → Prob

/-
## Conditional Expectation

The core primitive: E[f | g] represents the expected value of f
given (conditioned on) g.

We axiomatize this directly rather than defining via integration.
-/

axiom CondExp {α : Type} : ProbProp α → ProbProp α → Prob

notation "𝔼[" f " | " g "]" => CondExp f g

-- Axioms for conditional expectation

-- Normalization: E[1 | g] = 1 (when g is not identically 0)
axiom CondExp.norm {α : Type} (g : ProbProp α) :
  𝔼[(fun _ => 𝟙) | g] = 𝟙

-- Positivity: f ≥ 0 implies E[f | g] ≥ 0
-- (trivially satisfied since Prob ⊆ [0,1])

-- Monotonicity: if f ≤ f' pointwise, then E[f|g] ≤ E[f'|g]
axiom CondExp.mono {α : Type} (f f' g : ProbProp α) :
  (∀ x, f x ≤ₚ f' x) → 𝔼[f | g] ≤ₚ 𝔼[f' | g]

-- Product rule (Bayes): E[f·g | h] relates to E[f | g·h]·E[g | h]
-- This is the key compositional property
axiom CondExp.product {α : Type} (f g h : ProbProp α) :
  𝔼[(fun x => f x *ₚ g x) | h] = 𝔼[f | (fun x => g x *ₚ h x)] *ₚ 𝔼[g | h]

/-
## Probabilistic Entailment

Γ ⊢ₚ φ means: E[φ | Γ] ≥ p

This is our replacement for logical entailment.
-/

structure ProbEntails {α : Type} (Γ φ : ProbProp α) (p : Prob) : Prop where
  bound : 𝔼[φ | Γ] ≥ₚ p

notation:25 Γ " ⊢[" p "] " φ => ProbEntails Γ φ p

/-
## Derived Rules
-/

-- Axiom rule: φ ⊢[1] φ
theorem axiom_rule {α : Type} (φ : ProbProp α) : φ ⊢[𝟙] φ := by
  constructor
  -- E[φ | φ] = 1 by normalization (φ conditioned on itself)
  sorry

-- Cut rule: if Γ ⊢[p] φ and φ ⊢[q] ψ, then Γ ⊢[p*q] ψ
theorem cut_rule {α : Type} (Γ φ ψ : ProbProp α) (p q : Prob) :
  (Γ ⊢[p] φ) → (φ ⊢[q] ψ) → (Γ ⊢[p *ₚ q] ψ) := by
  intro h1 h2
  constructor
  -- Need: E[ψ | Γ] ≥ p * q
  -- From h1: E[φ | Γ] ≥ p
  -- From h2: E[ψ | φ] ≥ q
  -- Use product rule and monotonicity
  sorry

-- Weakening: adding conditions can only decrease probability
-- If Γ ⊢[p] φ, then Γ ∧ Δ ⊢[p'] φ for some p' ≤ p
-- (This is actually more subtle in probability - conditioning changes things)

/-
## Classical Logic as Special Case

When all probabilities are 0 or 1, we recover classical logic.
-/

def isClassical (p : Prob) : Prop := p = 𝟘 ∨ p = 𝟙

-- A proposition is classical if it only takes values 0 or 1
def ClassicalProp (α : Type) := { f : ProbProp α // ∀ x, isClassical (f x) }

-- Classical entailment: Γ ⊢ φ means Γ ⊢[1] φ
def ClassicalEntails {α : Type} (Γ φ : ClassicalProp α) : Prop :=
  (Γ.val ⊢[𝟙] φ.val)

/-
## Negation

Strong negation: P(A) = 0
Weak negation: sequence with P(Aₙ) → 0
-/

def StrongNeg {α : Type} (φ : ProbProp α) : Prop :=
  ∀ ψ : ProbProp α, 𝔼[φ | ψ] = 𝟘

-- For weak negation, we need sequences (deferred)

/-
## Next Steps

1. Fill in the sorry proofs
2. Add more derived rules
3. Explore what theorems we can prove
4. Test: can we state/prove Bayes' theorem as a meta-theorem?
5. Test: what does "excluded middle" look like here?
-/

-- Excluded middle in probabilistic setting:
-- For any φ, P(φ) + P(¬φ) = 1
-- This is an algebraic identity, not a logical principle!

axiom complement {α : Type} (φ : ProbProp α) :
  ∃ (neg_φ : ProbProp α), ∀ (ψ : ProbProp α),
    𝔼[φ | ψ] +ₚ 𝔼[neg_φ | ψ] = 𝟙
