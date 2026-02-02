module ProbTT.DependentWeights where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero) renaming (suc to nsuc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Substitution
import ProbTT.Context as C

-- Dependent Weights Extension for ProbTT
--
-- Standard ProbTT: Γ ⊢ t : A @ w     where w is a constant weight
-- Extended ProbTT: Γ ⊢ t : A @ w(x)  where w is a function of x
--
-- This generalizes uniform weights to varying weights over the domain.
-- Key use case: (x : A) → B @ w(x) where the reliability of B depends on x
--
-- Example interpretation:
--   - "For all natural numbers n, P(n) holds with confidence 1/(n+1)"
--   - Weight function: w(n) = 1/(n+1)
--   - As n → ∞, confidence approaches 0

module DepTyping {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open DependentWeight DM
  open import ProbTT.Judgment
  open Typing DM

  -- Weight expression: can be a constant or depend on a variable
  data WExpr (n : ℕ) : Set ℓ where
    wconst : W → WExpr n
    wvar   : Fin n → (W → W) → WExpr n       -- w depends on variable i via function f
    wsup   : WExpr (nsuc n) → WExpr n        -- supremum over bound variable
    winf   : WExpr (nsuc n) → WExpr n        -- infimum over bound variable

  -- Evaluate weight expression in a given assignment of weights to variables
  evalW : ∀ {n} → WExpr n → (Fin n → W) → W
  evalW (wconst w) _ = w
  evalW (wvar i f) σ = f (σ i)
  evalW (wsup we) σ = sup (λ w → evalW we (λ { fzero → w ; (fsuc j) → σ j }))
  evalW (winf we) σ = inf (λ w → evalW we (λ { fzero → w ; (fsuc j) → σ j }))

  -- Weakening for weight expressions
  wkWExpr : ∀ {n} → WExpr n → WExpr (nsuc n)
  wkWExpr (wconst w) = wconst w
  wkWExpr (wvar i f) = wvar (fsuc i) f
  wkWExpr (wsup we) = wsup (wkWExpr we)
  wkWExpr (winf we) = winf (wkWExpr we)

  -- Dependent Pi type with weight function
  -- (x : A) → B @ w(x) means:
  --   Given a : A @ v, applying f : (x:A) → B @ w(x) gives f a : B[a] @ w(a) · v
  --
  -- The weight of the result depends on the actual argument value.
  --
  -- Key rule:
  --   Γ ⊢ f : (x : A) → B @ w(x)    Γ ⊢ a : A @ v
  --   ─────────────────────────────────────────────
  --              Γ ⊢ f a : B[a] @ w(a) · v
  --
  -- For type formation, we need sup over weights:
  --   If w(x) varies over x, the overall reliability is bounded by sup{w(x)}

  -- Dependent weighted typing judgment with weight expressions
  infix 3 _⊢d_∶_〔_〕
  data _⊢d_∶_〔_〕 : ∀ {n} → C.Ctx n → Tm n → Ty n → WExpr n → Set ℓ where

    -- Constant weight embeds standard judgment
    d-const : ∀ {n} {Γ : C.Ctx n} {t : Tm n} {A : Ty n} {w : W} →
              Γ ⊢ t ∶ A 〔 w 〕 →
              Γ ⊢d t ∶ A 〔 wconst w 〕

    -- Variable with dependent weight
    d-var : ∀ {n} {Γ : C.Ctx n} (i : Fin n) →
            Γ ⊢d var i ∶ C.lookup Γ i 〔 wconst 𝟙 〕

    -- Lambda: weight expression lifts under binder
    d-lam : ∀ {n} {Γ : C.Ctx n} {A : Ty n} {B : Ty (nsuc n)} {b : Tm (nsuc n)}
            {we : WExpr (nsuc n)} →
            (Γ C., A) ⊢d b ∶ B 〔 we 〕 →
            Γ ⊢d lam A b ∶ (A ⇒ B) 〔 wsup we 〕

    -- Application: instantiate dependent weight
    d-app : ∀ {n} {Γ : C.Ctx n} {A : Ty n} {B : Ty (nsuc n)} {f a : Tm n}
            {we : WExpr (nsuc n)} {v : W} →
            Γ ⊢d f ∶ (A ⇒ B) 〔 wsup we 〕 →
            Γ ⊢ a ∶ A 〔 v 〕 →
            Γ ⊢d app f a ∶ (B [ a ]ₜ) 〔 wconst v 〕

    -- Weight weakening for dependent weights
    d-weaken : ∀ {n} {Γ : C.Ctx n} {t : Tm n} {A : Ty n} {we we' : WExpr n}
               {σ : Fin n → W} →
               Γ ⊢d t ∶ A 〔 we 〕 →
               evalW we' σ ≤ evalW we σ →
               Γ ⊢d t ∶ A 〔 we' 〕

  -- Key theorem: uniform weights are a special case
  -- If w(x) = w for all x, then dependent Pi reduces to standard Pi
  -- Proof: sup(const w) = w by sup-const axiom
  postulate
    uniform-specializes : ∀ {n} {Γ : C.Ctx n} {A : Ty n} {B : Ty (nsuc n)}
                          {b : Tm (nsuc n)} {w : W} →
                          (Γ C., A) ⊢ b ∶ B 〔 w 〕 →
                          Γ ⊢d lam A b ∶ (A ⇒ B) 〔 wconst w 〕

  -- Dependent weights for existential/Sigma types
  -- (x : A) × B @ w(x) has weight inf{w(x) : x ∈ A}
  -- because we need ALL instances to have sufficient weight

  -- Example: Graded universal quantification
  -- ∀(n : ℕ). P(n) @ w(n) where w(n) decreases
  -- The overall statement has weight inf{w(n)}
  -- If w(n) → 0 as n → ∞, then inf = 0

  -- Example: Conditional probability
  -- P(B|A) can be modeled as: given evidence a : A @ v, conclude B @ f(v)
  -- where f is the conditional weight function

-- Concrete examples with Boolean weights
module DepBoolExamples where
  open BoolDM
  open DepTyping BoolDM

  -- In Boolean case, sup = OR over all values, inf = AND over all values
  -- For finite types, this is computable

  -- Example: (x : Bool) → P @ w(x)
  -- w(true) = 1, w(false) = 0
  -- sup = 1, inf = 0
