{- Neighbourhood Semantics for CredTT

   Stability is a META-PROPERTY (like termination), not a judgment inside CredTT.
   We define:
   - Stable₁: robust inhabitation near credence 1
   - Unstable₀: fragile inhabitation near credence 0

   Key insight: classical proof techniques become stability theorems.
   The {0,1} collapse makes neighbourhoods trivial (singletons).

   AXIOM STATUS:
   Some stability lemmas are postulated because they require additional
   structure beyond the De Morgan algebra axioms (e.g., non-triviality 0 ≠ 1,
   monotonicity of multiplication, anti-monotonicity of negation).
-}
module CredTT.Neighbourhood where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open import CredTT.Credence

-- ============================================================================
-- STABILITY DEFINITIONS
-- ============================================================================

-- Stability near 1: inhabitation persists under degradation
-- Formal: ∃ c₀ < 1 . ∀ c ≥ c₀ . ∃ a . (Γ ⊢ a : A @ c)
-- This is a META-PROPERTY about derivability, not a judgment.

-- For a De Morgan algebra, we express stability order-theoretically:
-- c is stable near 1 if c is bounded away from 0

module StabilityDefs {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- Strictly less than (derived from order)
  _<_ : C → C → Set ℓ
  c < d = (c ≤ d) × (c ≡ d → ⊥)

  -- Strict positivity: c > 0
  Positive : C → Set ℓ
  Positive c = 𝟘 < c

  -- Strict sub-unity: c < 1
  SubUnity : C → Set ℓ
  SubUnity c = c < 𝟙

  -- Bounded away from zero: c ≥ c₀ for some c₀ > 0
  -- This captures persistence: small perturbations stay inhabited
  BoundedAwayFromZero : C → Set ℓ
  BoundedAwayFromZero c = Σ C (λ c₀ → Positive c₀ × (c₀ ≤ c))

  -- Bounded away from one: c ≤ c₁ for some c₁ < 1
  BoundedAwayFromOne : C → Set ℓ
  BoundedAwayFromOne c = Σ C (λ c₁ → SubUnity c₁ × (c ≤ c₁))

  -- ============================================================================
  -- STABILITY CLASSIFICATION
  -- ============================================================================

  -- Stable₁: robust near credence 1
  -- Operationally: the credence is bounded away from 0
  Stable₁ : C → Set ℓ
  Stable₁ = BoundedAwayFromZero

  -- Unstable₀: fragile near credence 0
  -- Operationally: the credence is bounded away from 1
  Unstable₀ : C → Set ℓ
  Unstable₀ = BoundedAwayFromOne

  -- Interior: neither extreme (strictly between 0 and 1)
  Interior : C → Set ℓ
  Interior c = Positive c × SubUnity c

  -- Stability classification type
  data Stability : C → Set ℓ where
    stable₁   : ∀ {c} → Stable₁ c → Stability c
    unstable₀ : ∀ {c} → Unstable₀ c → Stability c
    interior  : ∀ {c} → Interior c → Stability c

  -- ============================================================================
  -- POSTULATED LEMMAS (require additional axioms)
  -- ============================================================================

  -- Non-triviality: 0 ≠ 1 (required for meaningful stability)
  postulate
    𝟘≢𝟙 : 𝟘 ≡ 𝟙 → ⊥

  -- Anti-monotonicity of negation (order-reversing)
  postulate
    ¬-antitone : ∀ {c₁ c₂} → c₁ ≤ c₂ → ¬ c₂ ≤ ¬ c₁

  -- Monotonicity of multiplication
  postulate
    ·-mono : ∀ {a b c d} → a ≤ c → b ≤ d → (a · b) ≤ (c · d)

  -- Positivity of product (for product algebras like [0,1])
  postulate
    ·-positive : ∀ {c₁ c₂} → Positive c₁ → Positive c₂ → Positive (c₁ · c₂)

  -- ============================================================================
  -- BASIC STABILITY LEMMAS
  -- ============================================================================

  -- 1 is stable (trivially)
  𝟙-stable : Stable₁ 𝟙
  𝟙-stable = 𝟙 , (𝟙-greatest 𝟘 , 𝟘≢𝟙) , ≤-refl 𝟙

  -- 0 is unstable (trivially)
  𝟘-unstable : Unstable₀ 𝟘
  𝟘-unstable = 𝟘 , (𝟘-least 𝟙 , 𝟘≢𝟙) , ≤-refl 𝟘

  -- Multiplication preserves stability (key rule!)
  -- If c₁ and c₂ are stable, so is c₁ · c₂
  ·-preserves-stable : ∀ {c₁ c₂} → Stable₁ c₁ → Stable₁ c₂ → Stable₁ (c₁ · c₂)
  ·-preserves-stable {c₁} {c₂} (b₁ , pos₁ , bound₁) (b₂ , pos₂ , bound₂) =
    b₁ · b₂ , ·-positive pos₁ pos₂ , ·-mono bound₁ bound₂

  -- Negation flips stability
  -- Stable c implies Unstable (¬ c)
  ¬-flips-stable : ∀ {c} → Stable₁ c → Unstable₀ (¬ c)
  ¬-flips-stable {c} (b , (0≤b , 0≢b) , b≤c) =
    let ¬b≤¬0 : (¬ b) ≤ (¬ 𝟘)
        ¬b≤¬0 = ¬-antitone (𝟘-least b)
        ¬b≤1 : (¬ b) ≤ 𝟙
        ¬b≤1 = subst (λ x → (¬ b) ≤ x) ¬-𝟘 ¬b≤¬0
        ¬b≢1 : (¬ b) ≡ 𝟙 → ⊥
        -- If ¬b = 1, then ¬(¬b) = ¬1 = 0
        -- But ¬(¬b) = b (by involution), so b = 0
        -- But 0 ≢ b (from positivity of b)
        ¬b≢1 eq =
          let ¬¬b≡b : ¬ (¬ b) ≡ b
              ¬¬b≡b = ¬-invol b
              ¬1≡0 : ¬ 𝟙 ≡ 𝟘
              ¬1≡0 = ¬-𝟙
              -- ¬b ≡ 1 implies ¬(¬b) ≡ ¬1 ≡ 0
              ¬¬b≡0 : ¬ (¬ b) ≡ 𝟘
              ¬¬b≡0 = trans (cong ¬_ eq) ¬1≡0
              -- Combined with ¬¬b ≡ b, we get b ≡ 0
              b≡0 : b ≡ 𝟘
              b≡0 = trans (sym ¬¬b≡b) ¬¬b≡0
              -- But 0 ≢ b means 𝟘 ≡ b → ⊥
              0≡b : 𝟘 ≡ b
              0≡b = sym b≡0
          in 0≢b 0≡b
    in ¬ b , (¬b≤1 , ¬b≢1) , ¬-antitone b≤c

  -- Unstable (¬ c) implies Stable c (via double negation)
  unstable-neg-to-stable : ∀ {c} → Unstable₀ (¬ c) → Stable₁ c
  unstable-neg-to-stable {c} (b , (b≤1 , b≢1) , neg-c≤b) =
    let ¬b = ¬ b
        -- ¬ is antitone: neg-c ≤ b implies ¬b ≤ ¬¬c = c
        ¬b≤c : ¬ b ≤ c
        ¬b≤c = subst (λ x → ¬ b ≤ x) (¬-invol c) (¬-antitone neg-c≤b)
        -- ¬b > 0 because b < 1
        -- First: ¬-antitone (𝟙-greatest b) gives ¬𝟙 ≤ ¬b
        -- Then substitute ¬𝟙 = 𝟘 to get 𝟘 ≤ ¬b
        0≤¬b : 𝟘 ≤ ¬ b
        0≤¬b = subst (λ x → x ≤ ¬ b) ¬-𝟙 (¬-antitone (𝟙-greatest b))
        -- ¬b ≢ 0 because if ¬b = 0, then ¬(¬b) = ¬0 = 1, but ¬(¬b) = b, so b = 1
        -- contradicting b ≢ 1
        0≢¬b : 𝟘 ≡ ¬ b → ⊥
        0≢¬b eq =
          let -- From eq : 𝟘 ≡ ¬b, get ¬𝟘 ≡ ¬(¬b)
              ¬0≡¬¬b : ¬ 𝟘 ≡ ¬ (¬ b)
              ¬0≡¬¬b = cong ¬_ eq
              -- ¬𝟘 = 𝟙
              1≡¬¬b : 𝟙 ≡ ¬ (¬ b)
              1≡¬¬b = trans (sym ¬-𝟘) ¬0≡¬¬b
              -- ¬(¬b) = b
              1≡b : 𝟙 ≡ b
              1≡b = trans 1≡¬¬b (¬-invol b)
              -- So b = 1
              b≡1 : b ≡ 𝟙
              b≡1 = sym 1≡b
          in b≢1 b≡1
        ¬b-pos : Positive (¬ b)
        ¬b-pos = 0≤¬b , 0≢¬b
    in ¬ b , ¬b-pos , ¬b≤c

-- ============================================================================
-- BOOLEAN ALGEBRA SPECIALIZATION
-- ============================================================================

-- In Bool, stability classification is exhaustive and trivial
module BoolStability where
  open BoolDM
  open DeMorganAlgebra BoolDM
  open StabilityDefs BoolDM

  -- In {0,1}, neighbourhoods collapse to singletons
  -- true is stable, false is unstable, no interior points

  -- Classification is exhaustive for Bool
  bool-classify : (c : Bool) → (c ≡ true × Stable₁ c) ⊎ (c ≡ false × Unstable₀ c)
  bool-classify true  = inj₁ (refl , (true , (≤-true , (λ ())) , ≤-true))
  bool-classify false = inj₂ (refl , (false , (≤-false , (λ ())) , ≤-false))

  -- No interior points in Bool
  bool-no-interior : (c : Bool) → Interior c → ⊥
  bool-no-interior true  (pos , (c≤1 , c≢1)) = c≢1 refl
  bool-no-interior false ((0≤c , 0≢c) , _) = 0≢c refl

  -- Neighbourhood is trivial (singleton) for Bool
  bool-neighbourhood-trivial : (c : Bool) → Stable₁ c ⊎ Unstable₀ c
  bool-neighbourhood-trivial true  = inj₁ (true , (≤-true , (λ ())) , ≤-true)
  bool-neighbourhood-trivial false = inj₂ (false , (≤-false , (λ ())) , ≤-false)

-- ============================================================================
-- STABILITY THEOREMS FOR TYPE RULES
-- ============================================================================

-- These are meta-theorems about how stability propagates through derivations

module StabilityThms {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM

  -- Application is stability-preserving
  -- If f : A → B @ c₁ with Stable₁ c₁
  -- and a : A @ c₂ with Stable₁ c₂
  -- then f a : B @ c₁ · c₂ with Stable₁ (c₁ · c₂)
  app-stability : ∀ {c₁ c₂} →
    Stable₁ c₁ → Stable₁ c₂ →
    Stable₁ (c₁ · c₂)
  app-stability = ·-preserves-stable

  -- Π-introduction preserves stability
  -- If body has uniform stability, the lambda inherits it
  pi-intro-stability : ∀ {c} →
    Stable₁ c →
    Stable₁ c  -- Lambda at body credence
  pi-intro-stability stable-c = stable-c

  -- Σ-elimination preserves stability
  -- Projections don't degrade credence
  sigma-elim-stability : ∀ {c} →
    Stable₁ c →
    Stable₁ c
  sigma-elim-stability stable-c = stable-c

  -- Composition preserves stability
  -- g ∘ f @ c₁ · c₂ is stable if both are stable
  compose-stability : ∀ {c₁ c₂} →
    Stable₁ c₁ → Stable₁ c₂ →
    Stable₁ (c₁ · c₂)
  compose-stability = ·-preserves-stable

  -- Reductio: if ¬A is unstable, A is stable
  -- This is the stability version of proof by contradiction
  reductio : ∀ {c} →
    Unstable₀ (¬ c) →
    Stable₁ c
  reductio = unstable-neg-to-stable

  -- Contraposition: stability version (not exact equivalence)
  -- If c₁ ≤ c₂, then ¬c₂ ≤ ¬c₁
  contraposition-order : ∀ {c₁ c₂} →
    c₁ ≤ c₂ →
    ¬ c₂ ≤ ¬ c₁
  contraposition-order = ¬-antitone

  -- Ex falso: limit admissibility
  -- When c = 0, any conditional credence is admissible
  -- This is because c · d = 0 for any d when c = 0
  ex-falso-limit : ∀ (d : C) →
    𝟘 · d ≡ 𝟘
  ex-falso-limit d = ·-annihilˡ d

  -- Weakening: conditional on c = 1
  -- Adding assumptions at credence 1 preserves stability
  weakening-at-one : ∀ {c} →
    Stable₁ c →
    c · 𝟙 ≡ c →  -- Provided by ·-identityʳ
    Stable₁ c
  weakening-at-one stable-c _ = stable-c
