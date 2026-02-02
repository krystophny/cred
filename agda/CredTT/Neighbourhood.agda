{- Neighbourhood Semantics for CredTT

   FUNDAMENTAL INSIGHT:
   CredTT is NOT about assigning truth values.
   It is about HOW CREDENCE BEHAVES UNDER PROOF TRANSFORMATIONS.

   - Proof rules induce MONOTONE OPERATORS on credences
   - Proof structure induces ITERATION of these operators
   - "Stability" is about FIXED POINTS of these operators

   This is ORDER-THEORETIC DYNAMICS, not topology, not metrics.

   THREE DISTINCT NOTIONS (DO NOT CONFLATE):
   (A) Extremal credences: c = 1 (maximal), c = 0 (degenerate)
   (B) Interior credences: 0 < c < 1 (first-class citizens, NOT approximations)
   (C) Iteration behavior: what happens to c · sⁿ as n → ∞

   CRITICAL: We do NOT assume Archimedeanicity!
   In general De Morgan algebras:
   - s < 1 does NOT imply sⁿ → 0
   - There can be idempotents (s · s = s)
   - There can be plateaus (c · s = c with 0 < c < 1)
   - Multiple fixed points are possible

   These are NOT pathological - they are what makes CredTT richer than probability theory.
-}
module CredTT.Neighbourhood where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)

open import CredTT.Credence

-- ============================================================================
-- MONOTONE OPERATORS AND DYNAMICS
-- ============================================================================

-- Every proof step induces a monotone operator T_s : C → C
-- where T_s(c) = c · s

module DynamicsDefs {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- Strict order
  _<_ : C → C → Set ℓ
  c < d = (c ≤ d) × (c ≡ d → ⊥)

  -- Strict positivity: c > 0
  Positive : C → Set ℓ
  Positive c = 𝟘 < c

  -- Strict sub-unity: c < 1
  SubUnity : C → Set ℓ
  SubUnity c = c < 𝟙

  -- ============================================================================
  -- THE THREE KEY DEFINITIONS (order-theoretic, no Archimedean assumption)
  -- ============================================================================

  -- (1) Post-fixed point under step s:
  --     c ≤ c · s
  --     "Applying the proof step does not reduce credence"
  PostFixedPoint : C → C → Set ℓ
  PostFixedPoint c s = c ≤ (c · s)

  -- (2) Invariant under step s:
  --     c = c · s
  --     "Exact fixed point - step preserves credence exactly"
  Invariant : C → C → Set ℓ
  Invariant c s = c ≡ (c · s)

  -- (3) Degenerating under step s:
  --     infₙ (c · sⁿ) = 0
  --     "Credence collapses to 0 under iteration"
  --     For any positive lower bound, iteration eventually drops to or below it
  --     (Issue #77: Fixed from `→ ⊥` which gave the opposite meaning)
  Degenerating : C → C → Set ℓ
  Degenerating c s = ∀ (bound : C) → Positive bound →
                     Σ ℕ (λ n → (iterate n c s) ≤ bound)
    where
      iterate : ℕ → C → C → C
      iterate zero    c s = c
      iterate (suc n) c s = (iterate n c s) · s

  -- Iteration helper (exposed for use elsewhere)
  iterate : ℕ → C → C → C
  iterate zero    c s = c
  iterate (suc n) c s = (iterate n c s) · s

  -- ============================================================================
  -- STABILITY CLASSIFICATION (based on dynamics)
  -- ============================================================================

  -- Robust: credence is preserved or improved under all admissible steps
  -- This is broader than "c = 1"
  Robust : C → Set ℓ
  Robust c = Positive c × PostFixedPoint c 𝟙

  -- Vanishing: credence degenerates to 0
  Vanishing : C → Set ℓ
  Vanishing c = c ≡ 𝟘

  -- Idempotent: c · c = c (self-stable, may be interior!)
  Idempotent : C → Set ℓ
  Idempotent c = c ≡ (c · c)

  -- Interior: 0 < c < 1 (first-class citizen)
  Interior : C → Set ℓ
  Interior c = Positive c × SubUnity c

  -- Stability under a specific step
  -- Formulated using existential witness: c is stable under s if there exists
  -- a positive lower bound that all iterations stay above
  -- This avoids the need for infimum computation (complete lattice axioms)
  StableUnder : C → C → Set ℓ
  StableUnder c s = Σ C (λ bound → Positive bound × (∀ n → bound ≤ iterate n c s))

  _≢_ : C → C → Set ℓ
  x ≢ y = x ≡ y → ⊥

  -- ============================================================================
  -- PROPERTIES FROM DE MORGAN ALGEBRA AXIOMS
  -- ============================================================================
  -- These properties are now provided by DeMorganAlgebra in Credence.agda
  -- (previously postulated, now axioms - see issue #42, #147)

  -- Positivity preservation wrapper that matches the Positive type
  positive-preserved : ∀ {c₁ c₂} → Positive c₁ → Positive c₂ → Positive (c₁ · c₂)
  positive-preserved {c₁} {c₂} (0≤c₁ , 0≢c₁) (0≤c₂ , 0≢c₂) =
    DeMorganAlgebra.·-positive DM 0≤c₁ 0≢c₁ 0≤c₂ 0≢c₂

  -- ============================================================================
  -- TRIVIAL FIXED POINTS (extremal cases)
  -- ============================================================================

  -- 1 is a post-fixed point under step 1
  𝟙-postfixed-at-1 : PostFixedPoint 𝟙 𝟙
  𝟙-postfixed-at-1 = subst (𝟙 ≤_) (sym (·-identityʳ 𝟙)) (≤-refl 𝟙)  -- 1 ≤ 1·1 = 1

  -- 0 is invariant under any step
  𝟙-invariant-at-1 : Invariant 𝟙 𝟙
  𝟙-invariant-at-1 = sym (·-identityʳ 𝟙)  -- 1 = 1 · 1

  -- 0 is invariant under any step
  𝟘-invariant : ∀ (s : C) → Invariant 𝟘 s
  𝟘-invariant s = sym (·-annihilˡ s)  -- 0 = 0 · s

  -- ============================================================================
  -- IDEMPOTENT ELEMENTS (key to interior stability!)
  -- ============================================================================

  -- In a general De Morgan algebra, there may be idempotent elements e where e · e = e
  -- These are stable under iteration by themselves!

  -- If c is idempotent, iteration stabilizes immediately
  idempotent-stable : ∀ {c} → Idempotent c → Positive c →
                      ∀ (n : ℕ) → iterate n c c ≡ c
  idempotent-stable idemp pos zero    = refl
  idempotent-stable idemp pos (suc n) =
    trans (cong (λ x → x · _) (idempotent-stable idemp pos n)) (sym idemp)

  -- ============================================================================
  -- KEY INSIGHT: Interior credences can be stable!
  -- ============================================================================

  -- In non-Archimedean algebras, there exist c with 0 < c < 1 where c is stable
  -- Example: idempotent e with 0 < e < 1 satisfies e · e = e, so eⁿ = e

  -- Record for an interior stable element
  -- STATUS: VACUOUSLY SATISFIABLE in standard probability algebras
  --
  -- In [0,1] with standard multiplication, there are NO interior idempotents:
  --   - Idempotent: c · c = c implies c ∈ {0, 1}
  --   - Interior: 0 < c < 1
  --   - These are mutually exclusive in [0,1]!
  --
  -- This record exists to:
  --   1. Define the concept for non-standard algebras (e.g., idempotent semirings)
  --   2. State a negative result: no instances exist in probability algebras
  --   3. Support potential future extensions with different credence algebras
  --
  -- See bool-no-interior below for the proof that Bool has no interior points.
  record InteriorStable : Set ℓ where
    field
      elem     : C
      interior : Interior elem
      idemp    : Idempotent elem

-- ============================================================================
-- BOOLEAN ALGEBRA SPECIALIZATION (degenerate case)
-- ============================================================================

-- In Bool, there are NO interior points
-- This is the {0,1} collapse: CredTT becomes MLTT

module BoolDynamics where
  open BoolDM
  open DeMorganAlgebra BoolDM
  open DynamicsDefs BoolDM

  -- Bool has no interior points
  bool-no-interior : (c : Bool) → Interior c → ⊥
  bool-no-interior true  ((0≤c , 0≢c) , (c≤1 , c≢1)) = c≢1 refl
  bool-no-interior false ((0≤c , 0≢c) , _) = 0≢c refl

  -- Only two fixed points: 0 and 1
  bool-only-trivial-fixed : (c : Bool) → Idempotent c → (c ≡ true) ⊎ (c ≡ false)
  bool-only-trivial-fixed true  _ = inj₁ refl
  bool-only-trivial-fixed false _ = inj₂ refl

  -- Classification is exhaustive for Bool
  bool-classify : (c : Bool) → (c ≡ true) ⊎ (c ≡ false)
  bool-classify true  = inj₁ refl
  bool-classify false = inj₂ refl

  -- This is WHY {0,1} collapse works:
  -- In Bool, dynamics are trivial because there's nowhere else to go

-- ============================================================================
-- STABILITY THEOREMS FOR TYPE RULES
-- ============================================================================

module StabilityThms {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open DynamicsDefs DM

  -- These theorems require careful algebraic reasoning about associativity,
  -- commutativity, and monotonicity. We postulate them as axioms about
  -- well-behaved De Morgan algebras with multiplication.

  -- Application preserves post-fixed point property
  -- If c and d are both post-fixed under s, then c · d is post-fixed under s
  -- PROOF: c ≤ c·s implies c·d ≤ (c·s)·d = (c·d)·s by ·-mono and algebra laws
  --
  -- NOTE: The second hypothesis (PostFixedPoint d s) is unused in this proof.
  -- The signature preserves full generality for consistency with the theorem
  -- statement and potential alternative proofs that might use both hypotheses
  -- (e.g., proofs via d ≤ d·s with different rewriting strategies).
  app-preserves-postfixed : ∀ {c s d} →
    PostFixedPoint c s →
    PostFixedPoint d s →
    PostFixedPoint (c · d) s
  app-preserves-postfixed {c} {s} {d} c≤cs _ =
    -- Goal: c · d ≤ (c · d) · s
    -- Step 1: From c ≤ c·s and ≤-refl d, by ·-mono: c·d ≤ (c·s)·d
    -- Step 2: (c·s)·d = c·(s·d) = c·(d·s) = (c·d)·s by assoc and comm
    let step1 : c · d ≤ (c · s) · d
        step1 = ·-mono c≤cs (≤-refl d)
        -- Rewrite (c·s)·d to (c·d)·s
        rw1 : (c · s) · d ≡ c · (s · d)
        rw1 = ·-assoc c s d
        rw2 : c · (s · d) ≡ c · (d · s)
        rw2 = cong (c ·_) (·-comm s d)
        rw3 : c · (d · s) ≡ (c · d) · s
        rw3 = sym (·-assoc c d s)
        rw : (c · s) · d ≡ (c · d) · s
        rw = trans rw1 (trans rw2 rw3)
    in subst (c · d ≤_) rw step1

  -- Negation flips fixed points
  -- If c is a post-fixed point, ¬c is "post-unfixed"
  neg-flips : ∀ {c s} →
    PostFixedPoint c s →
    (¬ (c · s)) ≤ (¬ c)
  neg-flips c≤cs = ¬-antitone c≤cs

  -- Ex falso: 0 is always a fixed point (trivial dynamics)
  ex-falso : ∀ (s : C) → Invariant 𝟘 s
  ex-falso = 𝟘-invariant

  -- Weakening: 1 · c = c (no degradation when using at credence 1)
  weakening : ∀ (c : C) → 𝟙 · c ≡ c
  weakening = ·-identityˡ

-- ============================================================================
-- INDUCTION PRINCIPLE (order-theoretic formulation)
-- ============================================================================

module InductionDynamics {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open DynamicsDefs DM

  -- Induction is valid for predicates whose credence is a post-fixed point
  -- of the step operator.
  --
  -- Classical induction secretly assumes: step at credence 1
  -- CredTT makes this explicit: c ≤ c · s
  --
  -- This allows:
  -- - Induction at c = 1 (classical)
  -- - Induction at interior c (if c is idempotent or step-invariant)
  -- - Rejection of brittle induction (when c > c · s, step degrades)

  record InductionValid (c : C) (step : C) : Set ℓ where
    field
      base      : Positive c
      preserve  : PostFixedPoint c step

  -- Classical induction: step = 1
  classical-induction : ∀ {c} → Positive c → InductionValid c 𝟙
  classical-induction {c} pos = record
    { base = pos
    ; preserve = subst (c ≤_) (sym (·-identityʳ c)) (≤-refl c)
    }

  -- Interior induction: c is idempotent
  -- If c = c · c, then c ≤ c · c (post-fixed point)
  interior-induction : ∀ {c} → Interior c → Idempotent c → InductionValid c c
  interior-induction {c} (pos , _) idemp = record
    { base = pos
    ; preserve = subst (c ≤_) idemp (≤-refl c)  -- c ≤ c, subst along c = c·c
    }

-- ============================================================================
-- CLASSICAL RECOVERY (for backwards compatibility)
-- ============================================================================

-- Legacy definitions using old terminology
module StabilityDefs {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open DynamicsDefs DM public

  -- Bounded away from zero (legacy)
  BoundedAwayFromZero : C → Set ℓ
  BoundedAwayFromZero c = Σ C (λ c₀ → Positive c₀ × (c₀ ≤ c))

  -- Bounded away from one (legacy)
  BoundedAwayFromOne : C → Set ℓ
  BoundedAwayFromOne c = Σ C (λ c₁ → SubUnity c₁ × (c ≤ c₁))

  -- Legacy stability names
  Stable₁ : C → Set ℓ
  Stable₁ = BoundedAwayFromZero

  Unstable₀ : C → Set ℓ
  Unstable₀ = BoundedAwayFromOne

  -- Basic lemmas
  𝟙-stable : Stable₁ 𝟙
  𝟙-stable = 𝟙 , (𝟙-greatest 𝟘 , 𝟘≢𝟙) , ≤-refl 𝟙

  𝟘-unstable : Unstable₀ 𝟘
  𝟘-unstable = 𝟘 , (𝟘-least 𝟙 , 𝟘≢𝟙) , ≤-refl 𝟘

  ·-preserves-stable : ∀ {c₁ c₂} → Stable₁ c₁ → Stable₁ c₂ → Stable₁ (c₁ · c₂)
  ·-preserves-stable {c₁} {c₂} (b₁ , pos₁ , bound₁) (b₂ , pos₂ , bound₂) =
    b₁ · b₂ , positive-preserved pos₁ pos₂ , ·-mono bound₁ bound₂

  -- NOTE (Issue #137): ¬-flips-stable uses ¬-antitone, which is an AXIOM FIELD
  -- of DeMorganAlgebra (see Credence.agda:72), NOT a postulate. Each algebra
  -- instance must provide this field:
  -- - BoolDM: proven (notB-antitone)
  -- - IntervalDM: proven (¬F-antitone-proof)
  -- This proof is valid for any algebra that satisfies DeMorganAlgebra.
  ¬-flips-stable : ∀ {c} → Stable₁ c → Unstable₀ (¬ c)
  ¬-flips-stable {c} (b , (0≤b , 0≢b) , b≤c) =
    let ¬b≤¬0 : (¬ b) ≤ (¬ 𝟘)
        ¬b≤¬0 = ¬-antitone (𝟘-least b)
        ¬b≤1 : (¬ b) ≤ 𝟙
        ¬b≤1 = subst (λ x → (¬ b) ≤ x) ¬-𝟘 ¬b≤¬0
        ¬b≢1 : (¬ b) ≡ 𝟙 → ⊥
        ¬b≢1 eq =
          let ¬¬b≡b : ¬ (¬ b) ≡ b
              ¬¬b≡b = ¬-invol b
              ¬1≡0 : ¬ 𝟙 ≡ 𝟘
              ¬1≡0 = ¬-𝟙
              ¬¬b≡0 : ¬ (¬ b) ≡ 𝟘
              ¬¬b≡0 = trans (cong ¬_ eq) ¬1≡0
              b≡0 : b ≡ 𝟘
              b≡0 = trans (sym ¬¬b≡b) ¬¬b≡0
              0≡b : 𝟘 ≡ b
              0≡b = sym b≡0
          in 0≢b 0≡b
    in ¬ b , (¬b≤1 , ¬b≢1) , ¬-antitone b≤c

  -- Reverse direction: unstable negation implies stable
  -- If ¬c is bounded away from 1, then c is bounded away from 0
  unstable-neg-to-stable : ∀ {c} → Unstable₀ (¬ c) → Stable₁ c
  unstable-neg-to-stable {c} (b , (b≤1 , b≢1) , ¬c≤b) =
    let -- From b < 1, we get ¬b > 0
        0≤¬b : 𝟘 ≤ (¬ b)
        0≤¬b = subst (_≤ ¬ b) ¬-𝟙 (¬-antitone (𝟙-greatest b))
        -- ¬b ≠ 0 because b ≠ 1 (need 𝟘 ≡ ¬b → ⊥ for Positive)
        0≢¬b : 𝟘 ≡ (¬ b) → ⊥
        0≢¬b eq =
          let ¬¬b≡b : ¬ (¬ b) ≡ b
              ¬¬b≡b = ¬-invol b
              ¬0≡1 : ¬ 𝟘 ≡ 𝟙
              ¬0≡1 = ¬-𝟘
              -- from 0 ≡ ¬b, derive ¬0 ≡ ¬(¬b) = b
              ¬¬b≡¬0 : ¬ (¬ b) ≡ ¬ 𝟘
              ¬¬b≡¬0 = cong ¬_ (sym eq)
              b≡1 : b ≡ 𝟙
              b≡1 = trans (sym ¬¬b≡b) (trans ¬¬b≡¬0 ¬0≡1)
          in b≢1 b≡1
        -- From ¬c ≤ b, by antitone: ¬b ≤ ¬(¬c) = c
        ¬b≤c : (¬ b) ≤ c
        ¬b≤c = subst ((¬ b) ≤_) (¬-invol c) (¬-antitone ¬c≤b)
    in ¬ b , (0≤¬b , 0≢¬b) , ¬b≤c

-- Boolean specialization (stability view)
-- TECHNICAL DEBT: This module duplicates `bool-no-interior` from BoolDynamics.
-- See GitHub issue #102 for planned consolidation.
-- Temporary justification: kept separate during refactoring to preserve imports.
module BoolStability where
  open BoolDM
  open DeMorganAlgebra BoolDM
  open StabilityDefs BoolDM

  bool-classify : (c : Bool) → (c ≡ true × Stable₁ c) ⊎ (c ≡ false × Unstable₀ c)
  bool-classify true  = inj₁ (refl , (true , (≤-true , (λ ())) , ≤-true))
  bool-classify false = inj₂ (refl , (false , (≤-false , (λ ())) , ≤-false))

  bool-no-interior : (c : Bool) → Interior c → ⊥
  bool-no-interior true  (pos , (c≤1 , c≢1)) = c≢1 refl
  bool-no-interior false ((0≤c , 0≢c) , _) = 0≢c refl

  bool-neighbourhood-trivial : (c : Bool) → Stable₁ c ⊎ Unstable₀ c
  bool-neighbourhood-trivial true  = inj₁ (true , (≤-true , (λ ())) , ≤-true)
  bool-neighbourhood-trivial false = inj₂ (false , (≤-false , (λ ())) , ≤-false)

-- ============================================================================
-- INTERVAL [0,1] SPECIALIZATION
-- ============================================================================
-- Unlike Bool, the interval [0,1] has interior points and non-trivial dynamics.

module IntervalStability where
  open import CredTT.Interval
  open DeMorganAlgebra IntervalDM
  open StabilityDefs IntervalDM

  -- The Interval module defines Interior using ≈ (cross-multiplication equivalence)
  -- while DynamicsDefs.Positive uses ≡. We bridge them with postulates.
  -- See GitHub issue #189 for tracking proof of these postulates.

  postulate
    -- half is positive (0 < half in the dynamics sense)
    -- Proof requires bridging ≈-inequality to ≡-inequality; see issue #189
    half-positive : Positive half
    quarter-positive : Positive quarter

  -- In [0,1], half is an interior point
  half-stable : Stable₁ half
  half-stable = half , half-positive , ≤F-refl half

  -- Quarter is also interior
  quarter-stable : Stable₁ quarter
  quarter-stable = quarter , quarter-positive , ≤F-refl quarter

  -- Key difference from Bool: interior points exist!
  -- half-is-interior (from Interval) proves 0 < half < 1 using ≈-inequality

  -- In [0,1] with standard multiplication, iteration degenerates
  -- c * s^n → 0 for any s < 1 (Archimedean property)
  -- This contrasts with non-Archimedean algebras where interior stable points exist

  -- Demonstration: half is NOT idempotent
  -- Note: Idempotent from DynamicsDefs is c ≡ c · c
  -- no-interior-idempotent expects c · c ≡ c
  half-not-idempotent : Idempotent half → ⊥
  half-not-idempotent idemp = no-interior-idempotent half (sym idemp) half-is-interior

  -- Power of half: (1/2)^n approaches 0
  -- See GitHub issue #190 for tracking proof of these postulates.
  -- Solution: define power-of-half recursively and prove by induction.
  postulate
    power-of-half : ℕ → I
    power-of-half-zero : power-of-half 0 ≡ half
    power-of-half-suc : ∀ n → power-of-half (Data.Nat.suc n) ≡ power-of-half n ·I half
    half-iter-eq : ∀ n → iterate n half half ≡ power-of-half n

  half-degenerates : ∀ (n : ℕ) → iterate n half half ≡ power-of-half n
  half-degenerates = half-iter-eq

  -- Summary of [0,1] vs Bool:
  -- Bool: No interior points, trivial dynamics
  -- [0,1]: Infinitely many interior points, Archimedean dynamics (iteration degenerates)
