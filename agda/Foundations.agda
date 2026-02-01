{-# OPTIONS --postfix-projections #-}
-- Probabilistic Foundations in Agda
-- Probability as primitive, logic as derived
--
-- NOTE: We use postulates because we're axiomatizing probability
-- as a primitive notion. This is intentional - not a workaround.

module Foundations where

------------------------------------------------------------------------
-- Propositional Equality (needed early)
------------------------------------------------------------------------

open import Agda.Builtin.Equality public

------------------------------------------------------------------------
-- Probability Type (axiomatized)
------------------------------------------------------------------------

postulate
  Prob : Set
  𝟘 : Prob                         -- zero probability
  𝟙 : Prob                         -- certainty
  _≤ₚ_ : Prob → Prob → Set         -- probability ordering
  _+ₚ_ : Prob → Prob → Prob        -- addition (capped at 1)
  _*ₚ_ : Prob → Prob → Prob        -- multiplication
  _-ₚ_ : Prob → Prob → Prob        -- truncated subtraction

infixl 6 _+ₚ_ _-ₚ_
infixl 7 _*ₚ_
infix 4 _≤ₚ_

-- Basic ordering axioms
postulate
  ≤ₚ-refl : (p : Prob) → p ≤ₚ p
  ≤ₚ-trans : (p q r : Prob) → p ≤ₚ q → q ≤ₚ r → p ≤ₚ r
  ≤ₚ-antisym : (p q : Prob) → p ≤ₚ q → q ≤ₚ p → p ≡ q
  𝟘-min : (p : Prob) → 𝟘 ≤ₚ p
  𝟙-max : (p : Prob) → p ≤ₚ 𝟙

-- Multiplication axioms
postulate
  *ₚ-identityˡ : (p : Prob) → 𝟙 *ₚ p ≡ p
  *ₚ-identityʳ : (p : Prob) → p *ₚ 𝟙 ≡ p
  *ₚ-comm : (p q : Prob) → p *ₚ q ≡ q *ₚ p
  *ₚ-assoc : (p q r : Prob) → (p *ₚ q) *ₚ r ≡ p *ₚ (q *ₚ r)
  *ₚ-mono : (p₁ p₂ q₁ q₂ : Prob) → p₁ ≤ₚ q₁ → p₂ ≤ₚ q₂ → (p₁ *ₚ p₂) ≤ₚ (q₁ *ₚ q₂)

------------------------------------------------------------------------
-- Probabilistic Propositions
------------------------------------------------------------------------

-- A probabilistic proposition over a sample space A
-- assigns a probability value to each outcome
ProbProp : Set → Set
ProbProp A = A → Prob

------------------------------------------------------------------------
-- Conditional Expectation (axiomatized)
------------------------------------------------------------------------

-- The core primitive: E[f | g]
-- Expected value of f given (conditioned on) g

postulate
  𝔼[_∣_] : {A : Set} → ProbProp A → ProbProp A → Prob

-- Axioms for conditional expectation

postulate
  -- Normalization: E[1 | g] = 1
  𝔼-norm : {A : Set} (g : ProbProp A) → 𝔼[ (λ _ → 𝟙) ∣ g ] ≡ 𝟙

  -- Monotonicity: f ≤ f' pointwise implies E[f|g] ≤ E[f'|g]
  𝔼-mono : {A : Set} (f f' g : ProbProp A) →
           (∀ x → f x ≤ₚ f' x) → 𝔼[ f ∣ g ] ≤ₚ 𝔼[ f' ∣ g ]

  -- Product rule (Bayes): E[f·g | h] = E[f | g·h] · E[g | h]
  𝔼-product : {A : Set} (f g h : ProbProp A) →
              𝔼[ (λ x → f x *ₚ g x) ∣ h ] ≡
              𝔼[ f ∣ (λ x → g x *ₚ h x) ] *ₚ 𝔼[ g ∣ h ]

------------------------------------------------------------------------
-- Probabilistic Entailment
------------------------------------------------------------------------

-- Γ ⊢[p] φ means: E[φ | Γ] ≥ p
-- This is our replacement for logical entailment

record _⊢[_]_ {A : Set} (Γ : ProbProp A) (p : Prob) (φ : ProbProp A) : Set where
  constructor mk-entails
  field
    bound : p ≤ₚ 𝔼[ φ ∣ Γ ]

open _⊢[_]_ public

------------------------------------------------------------------------
-- Derived Rules
------------------------------------------------------------------------

-- Cut rule: if Γ ⊢[p] φ and φ ⊢[q] ψ, then Γ ⊢[p*q] ψ
-- This is the probabilistic version of transitivity

postulate
  cut-rule : {A : Set} {Γ φ ψ : ProbProp A} {p q : Prob} →
             Γ ⊢[ p ] φ →
             φ ⊢[ q ] ψ →
             Γ ⊢[ p *ₚ q ] ψ

-- The proof would use:
-- - E[ψ | Γ] ≥ E[ψ | φ] * E[φ | Γ] (chain rule / tower property)
-- - E[φ | Γ] ≥ p (from first premise)
-- - E[ψ | φ] ≥ q (from second premise)
-- - Monotonicity of multiplication

------------------------------------------------------------------------
-- Classical Logic as Special Case
------------------------------------------------------------------------

-- Disjoint union
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- Dependent pair
record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

-- A proposition is "classical" if it only takes values 0 or 1
isClassical : Prob → Set
isClassical p = (p ≡ 𝟘) ⊎ (p ≡ 𝟙)

ClassicalProp : Set → Set
ClassicalProp A = Σ (ProbProp A) (λ f → ∀ x → isClassical (f x))

-- Classical entailment: Γ ⊢ φ means Γ ⊢[1] φ
_⊢_ : {A : Set} → ProbProp A → ProbProp A → Set
Γ ⊢ φ = Γ ⊢[ 𝟙 ] φ

------------------------------------------------------------------------
-- Negation Spectrum
------------------------------------------------------------------------

-- Strong negation: E[φ | ψ] = 0 for all ψ
StrongNeg : {A : Set} → ProbProp A → Set
StrongNeg φ = ∀ ψ → 𝔼[ φ ∣ ψ ] ≡ 𝟘

-- Probabilistic complement: φ and ¬φ sum to 1
postulate
  complement : {A : Set} (φ : ProbProp A) →
               Σ (ProbProp A) (λ ¬φ → ∀ ψ → 𝔼[ φ ∣ ψ ] +ₚ 𝔼[ ¬φ ∣ ψ ] ≡ 𝟙)

-- Note: P(φ) + P(¬φ) = 1 is an algebraic identity
-- NOT a logical principle like excluded middle
-- We don't need to "decide" φ or ¬φ; we work with both weighted by probability

------------------------------------------------------------------------
-- Weak Negation (via sequences)
------------------------------------------------------------------------

-- For weak negation, we need sequences of propositions
-- P(φₙ) → 0 means φ becomes arbitrarily implausible

-- Natural numbers for indexing sequences
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- A sequence of probabilistic propositions
ProbPropSeq : Set → Set
ProbPropSeq A = ℕ → ProbProp A

-- Convergence to zero: for all ε > 0, eventually P(φₙ) < ε
-- We'd need a richer Prob type to express this properly
-- For now, we note this is the key concept for weak negation

------------------------------------------------------------------------
-- Excluded Middle: Probabilistic vs Classical
------------------------------------------------------------------------

-- Classical LEM: φ ∨ ¬φ (must decide)
-- Probabilistic: P(φ) + P(¬φ) = 1 (algebraic identity)

-- The "decision" is replaced by a constraint
-- We can work with both possibilities weighted by probability

-- This is why probability might avoid the LEM debate:
-- We never need to assert φ or ¬φ
-- We just assign weights that sum to 1

------------------------------------------------------------------------
-- Future Work
------------------------------------------------------------------------

-- 1. Fill in proofs (replace postulates with constructions)
-- 2. Define Borel-Cantelli as a proof rule
-- 3. Explore probabilistic Zorn's lemma
-- 4. Connect to Markov categories
-- 5. Build computational content (sampling semantics)
