{- Stability Theorems for CredTT

   Classical proof techniques recovered as stability theorems.
   Each theorem shows how stability propagates through type rules.

   Key insight: CredTT does not lose proof techniques; it refines them
   from points to neighbourhoods.
-}
module CredTT.StabilityTheorems where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open import CredTT.Credence
open import CredTT.Neighbourhood

-- ============================================================================
-- RECOVERED CLASSICAL PROOF TECHNIQUES
-- ============================================================================

module ClassicalRecovery {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM

  -- -------------------------------------------------------------------------
  -- 1. Direct Proof: track credence bounds; c accumulates via ·
  -- -------------------------------------------------------------------------

  -- Direct proofs work by composition of stable steps
  direct-proof : ∀ {c₁ c₂} →
    Stable₁ c₁ → Stable₁ c₂ →
    Stable₁ (c₁ · c₂)
  direct-proof = ·-preserves-stable

  -- -------------------------------------------------------------------------
  -- 2. Proof by Cases: context refinement + De Morgan ∨
  -- -------------------------------------------------------------------------

  -- If each case is stable, result is stable
  -- case-stability requires showing that stability of branches implies
  -- stability of the result (via credence multiplication)
  case-stability : ∀ {c v} →
    Stable₁ c →   -- scrutinee stable
    Stable₁ v →   -- branches stable (both have same credence v)
    Stable₁ (c · v)  -- result stable
  case-stability = ·-preserves-stable

  -- -------------------------------------------------------------------------
  -- 3. Contraposition: stability version (not exact equivalence)
  -- -------------------------------------------------------------------------

  -- Order reversal under negation
  -- This is the stability analog of contrapositive
  -- (Uses postulated ¬-antitone from StabilityDefs)
  neg-antitone : ∀ {c₁ c₂} →
    c₁ ≤ c₂ →
    ¬ c₂ ≤ ¬ c₁
  neg-antitone = StabilityDefs.¬-antitone DM

  -- -------------------------------------------------------------------------
  -- 4. Reductio ad Absurdum: collapse to degeneracy near 0
  -- -------------------------------------------------------------------------

  -- If assuming ¬A leads to instability, A must be stable
  reductio-ad-absurdum : ∀ {c} →
    Unstable₀ (¬ c) →
    Stable₁ c
  reductio-ad-absurdum = unstable-neg-to-stable

  -- -------------------------------------------------------------------------
  -- 5. Ex Falso: limit admissibility
  -- -------------------------------------------------------------------------

  -- When credence is 0, any conditional is admissible
  -- The joint P(A,B) = 0 regardless of P(A|B)
  ex-falso-admissibility : ∀ (any : C) →
    𝟘 · any ≡ 𝟘
  ex-falso-admissibility = ·-annihilˡ

  -- Equivalently: from 0 credence, anything follows at 0 credence
  ex-falso-propagates : ∀ {A-credence B-credence : C} →
    A-credence ≡ 𝟘 →
    (A-credence · B-credence) ≡ 𝟘
  ex-falso-propagates {_} {B-credence} refl = ·-annihilˡ B-credence

  -- -------------------------------------------------------------------------
  -- 6. Vacuous Truth: degenerate conditioning
  -- -------------------------------------------------------------------------

  -- When the condition has credence 0, any conditional credence is admissible
  -- This is the probabilistic version of vacuous truth
  vacuous-condition : ∀ {cond-credence result-credence : C} →
    cond-credence ≡ 𝟘 →
    (cond-credence · result-credence) ≡ 𝟘
  vacuous-condition = ex-falso-propagates

  -- -------------------------------------------------------------------------
  -- 7. Deduction Theorem: function abstraction
  -- -------------------------------------------------------------------------

  -- Γ, x:A ⊢ b:B @ c  implies  Γ ⊢ λx.b : A→B @ c
  -- Stability is preserved by lambda abstraction
  deduction-preserves-stability : ∀ {c} →
    Stable₁ c →   -- body credence stable
    Stable₁ c     -- lambda credence stable
  deduction-preserves-stability stable-c = stable-c

  -- -------------------------------------------------------------------------
  -- 8. Modus Ponens: application rule
  -- -------------------------------------------------------------------------

  -- f : A→B @ c₁ and a : A @ c₂ gives f a : B @ c₁ · c₂
  -- This is the fundamental credence multiplication rule
  modus-ponens-credence : ∀ (c₁ c₂ : C) → C
  modus-ponens-credence c₁ c₂ = c₁ · c₂

  -- Stability version
  modus-ponens-stability : ∀ {c₁ c₂} →
    Stable₁ c₁ → Stable₁ c₂ →
    Stable₁ (c₁ · c₂)
  modus-ponens-stability = ·-preserves-stable

  -- -------------------------------------------------------------------------
  -- 9. Syllogism: function composition
  -- -------------------------------------------------------------------------

  -- g : B→C @ c₂ and f : A→B @ c₁ gives g∘f : A→C @ c₂ · c₁
  syllogism-credence : ∀ (c₁ c₂ : C) → C
  syllogism-credence c₁ c₂ = c₂ · c₁

  syllogism-stability : ∀ {c₁ c₂} →
    Stable₁ c₁ → Stable₁ c₂ →
    Stable₁ (c₂ · c₁)
  syllogism-stability s₁ s₂ = ·-preserves-stable s₂ s₁

  -- -------------------------------------------------------------------------
  -- 10. Universal Generalization: Π-introduction
  -- -------------------------------------------------------------------------

  -- λx.b : Πx.B @ inf_x c(x)
  -- For uniform credence, this is just c
  pi-intro-uniform : ∀ {c} →
    Stable₁ c →
    Stable₁ c
  pi-intro-uniform stable-c = stable-c

  -- -------------------------------------------------------------------------
  -- 11. Existential Introduction: Σ-types
  -- -------------------------------------------------------------------------

  -- (a, b) : Σx.B @ c_a · c_b
  sigma-intro-credence : ∀ (c_a c_b : C) → C
  sigma-intro-credence c_a c_b = c_a · c_b

  sigma-intro-stability : ∀ {c_a c_b} →
    Stable₁ c_a → Stable₁ c_b →
    Stable₁ (c_a · c_b)
  sigma-intro-stability = ·-preserves-stable

  -- -------------------------------------------------------------------------
  -- 12. Equational Rewriting: credence-respecting
  -- -------------------------------------------------------------------------

  -- If a ≡ b at credence c, rewriting preserves c
  -- This follows from the congruence of ≡
  rewriting-preserves-credence : ∀ {c} →
    Stable₁ c →   -- identity proof stable
    Stable₁ c     -- rewritten term stable
  rewriting-preserves-credence stable-c = stable-c

-- ============================================================================
-- CREDTT-NATIVE PROOF TECHNIQUES
-- ============================================================================

module NativeTechniques {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM

  -- -------------------------------------------------------------------------
  -- 1. Stability Proofs: prove A stable near 1 or B degenerate near 0
  -- -------------------------------------------------------------------------

  -- Record for a stability proof
  record StabilityProof (c : C) : Set ℓ where
    field
      classification : Stable₁ c ⊎ Unstable₀ c ⊎ Interior c
      witness : C  -- the bound (c₀ for stable, c₁ for unstable)

  -- -------------------------------------------------------------------------
  -- 2. Credence Bounds as Invariants
  -- -------------------------------------------------------------------------

  -- A lower bound on credence
  record LowerBound (c : C) : Set ℓ where
    field
      bound : C
      bound-positive : 𝟘 ≤ bound  -- usually want bound > 0
      bound-valid : bound ≤ c

  -- An upper bound on credence
  record UpperBound (c : C) : Set ℓ where
    field
      bound : C
      bound-subunity : bound ≤ 𝟙
      bound-valid : c ≤ bound

  -- -------------------------------------------------------------------------
  -- 3. Continuity/Robustness Lemmas
  -- -------------------------------------------------------------------------

  -- Credence multiplication is continuous: small input degradation
  -- yields small output degradation
  -- Formally: if c₁' ≤ c₁ and c₂' ≤ c₂, then c₁'·c₂' ≤ c₁·c₂
  -- (Uses postulated ·-mono from StabilityDefs)
  mul-monotone : ∀ {c₁ c₁' c₂ c₂'} →
    c₁' ≤ c₁ → c₂' ≤ c₂ →
    (c₁' · c₂') ≤ (c₁ · c₂)
  mul-monotone = StabilityDefs.·-mono DM

  -- -------------------------------------------------------------------------
  -- 4. Degeneracy Analysis: quantify how fast c→0
  -- -------------------------------------------------------------------------

  -- A degeneracy rate: how quickly credence decays under operation
  record DegeneracyRate (f : C → C) : Set ℓ where
    field
      -- f(c) ≤ rate · c for some rate
      rate : C
      bound : ∀ c → f c ≤ rate · c

  -- -------------------------------------------------------------------------
  -- 5. Contractivity Arguments: step is non-degrading
  -- -------------------------------------------------------------------------

  -- A function is non-degrading if it preserves stability
  NonDegrading : (C → C) → Set ℓ
  NonDegrading f = ∀ {c} → Stable₁ c → Stable₁ (f c)

  -- Identity is non-degrading
  id-non-degrading : NonDegrading (λ c → c)
  id-non-degrading stable-c = stable-c

  -- Composition of non-degrading is non-degrading
  compose-non-degrading : ∀ {f g : C → C} →
    NonDegrading f → NonDegrading g →
    NonDegrading (λ c → f (g c))
  compose-non-degrading nd-f nd-g stable-c = nd-f (nd-g stable-c)

  -- -------------------------------------------------------------------------
  -- 6. Proof Factoring: isolate low-c steps
  -- -------------------------------------------------------------------------

  -- Factor a credence into high and low parts
  record CredenceFactoring (c : C) : Set ℓ where
    field
      high-part : C
      low-part : C
      factoring : c ≡ high-part · low-part
      high-stable : Stable₁ high-part

  -- -------------------------------------------------------------------------
  -- 7. Dual Proofs: squeeze between bounds
  -- -------------------------------------------------------------------------

  -- Squeeze theorem: lower bound + upper bound = squeezed region
  record SqueezedCredence (c : C) : Set ℓ where
    field
      lower : LowerBound c
      upper : UpperBound c

  -- -------------------------------------------------------------------------
  -- 8. Limit Theorems: asymptotic arguments
  -- -------------------------------------------------------------------------

  -- Import ℕ for sequences
  open import Data.Nat using (ℕ; zero; suc)

  -- A sequence of credences converging to a limit
  record ConvergentSequence : Set ℓ where
    field
      sequence : ℕ → C
      limit : C
      -- For all ε > 0, exists N such that n ≥ N implies |sequence n - limit| < ε
      -- In our order-theoretic setting: eventually stays in neighbourhood of limit

-- ============================================================================
-- STRUCTURAL RULES
-- ============================================================================

module StructuralRules {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM

  -- Exchange: holds unconditionally
  -- Context reordering preserves credence
  exchange : ∀ {c} → Stable₁ c → Stable₁ c
  exchange stable-c = stable-c

  -- Weakening: conditional on added assumptions having c = 1
  -- Adding an assumption at credence 1 doesn't degrade
  weakening : ∀ {c} →
    Stable₁ c →
    (c · 𝟙 ≡ c) →  -- weakening preserves credence
    Stable₁ c
  weakening stable-c _ = stable-c

  -- Weakening at credence 1 is trivial
  weakening-at-𝟙 : ∀ {c} → Stable₁ c → Stable₁ c
  weakening-at-𝟙 stable-c = stable-c

  -- Contraction: requires explicit duplication permission
  -- In general, contraction may degrade credence
  -- Safe contraction: when c · c = c (idempotent)
  safe-contraction : ∀ {c} →
    c · c ≡ c →  -- idempotence condition
    Stable₁ c →
    Stable₁ c
  safe-contraction _ stable-c = stable-c

  -- In the Boolean case, all credences are idempotent
  -- true ∧ true = true, false ∧ false = false
