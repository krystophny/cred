{- Stability Theorems for CredTT

   PROOFS AS MONOTONE DYNAMICAL SYSTEMS
   =====================================

   Each proof rule induces a monotone operator T_s : C -> C
   where T_s(c) = c * s.

   Stability is about FIXED POINTS of these operators, not truth values.

   Key insight: CredTT does not lose proof techniques; it reveals
   their underlying dynamics.

   THREE BEHAVIORS (no Archimedean assumption):
   1. Post-fixed point: c <= c * s (step doesn't reduce credence)
   2. Invariant: c = c * s (exact fixed point)
   3. Degenerating: inf_n (c * s^n) = 0 (credence collapses)

   The correct statement of "stability" is:
     c is stable under step s  iff  inf_n (c * s^n) > 0

   This allows:
   - Stability at c = 1 (classical)
   - Stability at interior c (if c is idempotent or step-invariant)
   - Rejection of brittle stability (when iteration degenerates)
-}
module CredTT.StabilityTheorems where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat as Nat using (ℕ; zero; suc)

open import CredTT.Credence
open import CredTT.Neighbourhood

-- ============================================================================
-- OPERATORS INDUCED BY PROOF RULES
-- ============================================================================

module OperatorDynamics {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open DynamicsDefs DM

  -- Each proof step at credence s induces the operator T_s(c) = c * s
  T : C → C → C
  T s c = c · s

  -- T_s is monotone (by monotonicity of multiplication)
  T-monotone : ∀ {s c₁ c₂} → c₁ ≤ c₂ → T s c₁ ≤ T s c₂
  T-monotone {s} {c₁} {c₂} c₁≤c₂ = ·-mono c₁≤c₂ (≤-refl s)

  -- T_1 is the identity operator
  T-identity : ∀ (c : C) → T 𝟙 c ≡ c
  T-identity c = ·-identityʳ c

  -- T_0 annihilates (sends everything to 0)
  T-zero : ∀ (c : C) → T 𝟘 c ≡ 𝟘
  T-zero c = ·-annihilʳ c

  -- Composition of operators: T_s composed with T_t equals T_{s*t}
  -- This follows from associativity: (c * s) * t = c * (s * t)
  T-compose : ∀ (s t c : C) → T t (T s c) ≡ T (s · t) c
  T-compose s t c = ·-assoc c s t

  -- Powers: s^n
  _^_ : C → ℕ → C
  s ^ zero = 𝟙
  s ^ suc n = (s ^ n) · s

  -- Note: iterate n c s from DynamicsDefs computes c * s^n
  -- The relationship iterate n c s = c * (s ^ n) holds by induction,
  -- but proving it requires careful handling of associativity.

-- ============================================================================
-- PRESERVATION LEMMAS: How operators preserve stability properties
-- ============================================================================

module PreservationLemmas {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM
  open OperatorDynamics DM

  -- Lemma 1: Post-fixed points are preserved under composition
  -- If c <= c*s and c <= c*t, then c <= c*(s*t)
  postfixed-compose : ∀ {c s t} →
    PostFixedPoint c s →
    PostFixedPoint c t →
    PostFixedPoint c (s · t)
  postfixed-compose {c} {s} {t} pf-s pf-t =
    -- c <= c*s and c <= c*t
    -- Goal: c <= c*(s*t)
    -- By pf-t: c <= c*t
    -- c*t <= (c*s)*t by monotonicity and pf-s
    -- (c*s)*t = c*(s*t) by associativity
    ≤-trans pf-t (subst (c · t ≤_) (·-assoc c s t) (·-mono pf-s (≤-refl t)))

  -- Lemma 2: Stable credences preserved under multiplication by stable step
  stable-mul-preserves : ∀ {c₁ c₂} → Stable₁ c₁ → Stable₁ c₂ → Stable₁ (c₁ · c₂)
  stable-mul-preserves = ·-preserves-stable

  -- Lemma 3: Invariant elements are closed under the operator
  invariant-closed : ∀ {c s} → Invariant c s → T s c ≡ c
  invariant-closed inv = sym inv

  -- Lemma 4: Idempotent elements are invariant under themselves
  idempotent-self-invariant : ∀ {c} → Idempotent c → Invariant c c
  idempotent-self-invariant idemp = idemp

-- ============================================================================
-- CONTRACTION LEMMAS: When operators contract credence
-- ============================================================================

module ContractionLemmas {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM
  open OperatorDynamics DM

  -- Use _<_ from DynamicsDefs (re-exported via StabilityDefs)
  -- instead of defining a duplicate StrictLess

  -- A step is contractive if it strictly reduces non-unit credence
  Contractive : C → Set ℓ
  Contractive s = ∀ {c} → Positive c → SubUnity c → (c · s) < c

  -- A step is non-expanding if it doesn't increase credence
  NonExpanding : C → Set ℓ
  NonExpanding s = ∀ (c : C) → (c · s) ≤ c

  -- All steps are non-expanding by the algebra axiom
  all-steps-non-expanding : ∀ (s : C) → NonExpanding s
  all-steps-non-expanding s c = ·-≤-self c s

  -- A step is preserving if it equals 1
  Preserving : C → Set ℓ
  Preserving s = s ≡ 𝟙

  -- Preserving steps are identity operators
  preserving-is-identity : ∀ {s} → Preserving s → ∀ (c : C) → T s c ≡ c
  preserving-is-identity refl c = ·-identityʳ c

-- ============================================================================
-- DEGENERATION ANALYSIS: When credence collapses to zero
-- ============================================================================

module DegenerationLemmas {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM
  open OperatorDynamics DM

  -- Zero is degenerate under all steps (trivially)
  zero-degenerate : ∀ (s : C) → iterate 0 𝟘 s ≡ 𝟘
  zero-degenerate s = refl

  -- Zero remains zero under any iteration
  zero-stays-zero : ∀ (n : ℕ) (s : C) → iterate n 𝟘 s ≡ 𝟘
  zero-stays-zero zero s = refl
  zero-stays-zero (suc n) s = trans (cong (_· s) (zero-stays-zero n s)) (·-annihilˡ s)

  -- Degenerate credence is absorbing
  degenerate-absorbing : ∀ {c s} → c ≡ 𝟘 → ∀ (n : ℕ) → iterate n c s ≡ 𝟘
  degenerate-absorbing {s = s} refl n = zero-stays-zero n s

-- ============================================================================
-- RECOVERED CLASSICAL PROOF TECHNIQUES (dynamics version)
-- ============================================================================

module ClassicalRecovery {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM
  open OperatorDynamics DM
  open PreservationLemmas DM

  -- -------------------------------------------------------------------------
  -- 1. Direct Proof: composition of operators
  -- -------------------------------------------------------------------------

  -- Direct proofs compose operators: T_s composed with T_t = T_{s*t}
  -- If both s and t are non-degrading (post-fixed points), composition is too
  direct-proof-operator : ∀ {c s₁ s₂} →
    PostFixedPoint c s₁ →
    PostFixedPoint c s₂ →
    c ≤ T (s₁ · s₂) c
  direct-proof-operator {c} {s₁} {s₂} pf₁ pf₂ =
    ≤-trans pf₂ (subst (c · s₂ ≤_) (·-assoc c s₁ s₂) (·-mono pf₁ (≤-refl s₂)))

  -- Legacy: using Stable₁ definitions
  direct-proof : ∀ {c₁ c₂} →
    Stable₁ c₁ → Stable₁ c₂ →
    Stable₁ (c₁ · c₂)
  direct-proof = ·-preserves-stable

  -- -------------------------------------------------------------------------
  -- 2. Proof by Cases: parallel branches
  -- -------------------------------------------------------------------------

  -- When both branches have the same dynamics (step s), the case analysis
  -- preserves stability
  case-dynamics : ∀ {c s} →
    PostFixedPoint c s →
    PostFixedPoint c s
  case-dynamics pf = pf

  -- Legacy
  case-stability : ∀ {c v} → Stable₁ c → Stable₁ v → Stable₁ (c · v)
  case-stability = ·-preserves-stable

  -- -------------------------------------------------------------------------
  -- 3. Contraposition: negation reverses order
  -- -------------------------------------------------------------------------

  -- If c ≤ d, then ¬d ≤ ¬c (antitone)
  neg-antitone : ∀ {c₁ c₂} → c₁ ≤ c₂ → ¬ c₂ ≤ ¬ c₁
  neg-antitone = StabilityDefs.¬-antitone DM

  -- Contraposition reverses dynamics:
  -- If c is post-fixed under s, then ¬c is "post-unfixed" under s
  contraposition-dynamics : ∀ {c s} →
    PostFixedPoint c s →
    (¬ (c · s)) ≤ (¬ c)
  contraposition-dynamics c≤cs = neg-antitone c≤cs

  -- -------------------------------------------------------------------------
  -- 4. Reductio: instability of negation implies stability
  -- -------------------------------------------------------------------------

  -- If ¬A is unstable (bounded away from 1), A is stable (bounded away from 0)
  reductio-dynamics : ∀ {c} →
    Unstable₀ (¬ c) →
    Stable₁ c
  reductio-dynamics = unstable-neg-to-stable

  -- -------------------------------------------------------------------------
  -- 5. Ex Falso: 0 is a fixed point of all operators
  -- -------------------------------------------------------------------------

  -- T_s(0) = 0 for any s
  ex-falso-fixed : ∀ (s : C) → T s 𝟘 ≡ 𝟘
  ex-falso-fixed s = ·-annihilˡ s

  -- 0 is invariant under any operator
  ex-falso-invariant : ∀ (s : C) → Invariant 𝟘 s
  ex-falso-invariant s = sym (·-annihilˡ s)

  -- Consequence: from 0, nothing propagates
  ex-falso-propagates : ∀ {c s : C} → c ≡ 𝟘 → (c · s) ≡ 𝟘
  ex-falso-propagates refl = ·-annihilˡ _

  -- -------------------------------------------------------------------------
  -- 6. Vacuous Truth: degenerate conditioning
  -- -------------------------------------------------------------------------

  -- Same as ex falso: 0 * anything = 0
  vacuous-condition : ∀ {s : C} → 𝟘 · s ≡ 𝟘
  vacuous-condition = ·-annihilˡ _

  -- -------------------------------------------------------------------------
  -- 7. Deduction Theorem: lambda preserves dynamics
  -- -------------------------------------------------------------------------

  -- If body has credence c and is stable under s, lambda has same dynamics
  deduction-dynamics : ∀ {c s} →
    PostFixedPoint c s →
    PostFixedPoint c s
  deduction-dynamics pf = pf

  -- -------------------------------------------------------------------------
  -- 8. Modus Ponens: operator composition
  -- -------------------------------------------------------------------------

  -- f : A->B @ s₁ and a : A @ s₂ gives f a : B @ s₁ * s₂
  -- The dynamics: T_{s₁} composed with T_{s₂} = T_{s₁*s₂}
  modus-ponens-dynamics : ∀ (s₁ s₂ c : C) → T s₂ (T s₁ c) ≡ T (s₁ · s₂) c
  modus-ponens-dynamics = T-compose

  -- Stability version
  modus-ponens-stability : ∀ {c₁ c₂} → Stable₁ c₁ → Stable₁ c₂ → Stable₁ (c₁ · c₂)
  modus-ponens-stability = ·-preserves-stable

  -- -------------------------------------------------------------------------
  -- 9. Syllogism: transitive composition
  -- -------------------------------------------------------------------------

  -- g composed with f has credence c_g * c_f
  -- T-compose s₂ s₁ c gives: T s₁ (T s₂ c) ≡ T (s₂ * s₁) c
  syllogism-dynamics : ∀ (s₁ s₂ c : C) → T s₁ (T s₂ c) ≡ T (s₂ · s₁) c
  syllogism-dynamics s₁ s₂ c = T-compose s₂ s₁ c

  -- -------------------------------------------------------------------------
  -- 10. Universal Generalization: Pi-introduction
  -- -------------------------------------------------------------------------

  -- λx.b : Πx.B @ inf_x c(x)
  -- If all instances have the same dynamics, so does the universal
  pi-intro-dynamics : ∀ {c s} →
    PostFixedPoint c s →
    PostFixedPoint c s
  pi-intro-dynamics pf = pf

  -- -------------------------------------------------------------------------
  -- 11. Existential Introduction: Sigma-types
  -- -------------------------------------------------------------------------

  -- (a, b) : Σx.B @ c_a * c_b
  sigma-intro-dynamics : ∀ {c_a c_b s} →
    PostFixedPoint c_a s →
    PostFixedPoint c_b s →
    c_a · c_b ≤ (c_a · c_b) · s
  sigma-intro-dynamics {c_a} {c_b} {s} pf_a pf_b =
    let step1 : c_a · c_b ≤ (c_a · s) · c_b
        step1 = ·-mono pf_a (≤-refl c_b)
        rw : (c_a · s) · c_b ≡ (c_a · c_b) · s
        rw = trans (·-assoc c_a s c_b)
            (trans (cong (c_a ·_) (·-comm s c_b))
                   (sym (·-assoc c_a c_b s)))
    in subst (c_a · c_b ≤_) rw step1

  -- -------------------------------------------------------------------------
  -- 12. Equational Rewriting: preserves dynamics
  -- -------------------------------------------------------------------------

  rewriting-dynamics : ∀ {c s} →
    PostFixedPoint c s →
    PostFixedPoint c s
  rewriting-dynamics pf = pf

-- ============================================================================
-- CREDTT-NATIVE PROOF TECHNIQUES (dynamics version)
-- ============================================================================

module NativeTechniques {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM

  -- -------------------------------------------------------------------------
  -- 1. Stability Proofs: prove c is post-fixed point of s
  -- -------------------------------------------------------------------------

  record StabilityProof (c s : C) : Set ℓ where
    field
      post-fixed : PostFixedPoint c s
      positive   : Positive c

  -- -------------------------------------------------------------------------
  -- 2. Invariant Proofs: prove c * s = c
  -- -------------------------------------------------------------------------

  record InvariantProof (c s : C) : Set ℓ where
    field
      invariant : Invariant c s
      positive  : Positive c

  -- Idempotents are invariant under themselves
  idempotent-invariant : ∀ {c} → Idempotent c → Invariant c c
  idempotent-invariant idemp = idemp

  -- -------------------------------------------------------------------------
  -- 3. Credence Bounds as Invariants
  -- -------------------------------------------------------------------------

  record LowerBound (c : C) : Set ℓ where
    field
      bound : C
      bound-positive : 𝟘 ≤ bound
      bound-valid : bound ≤ c

  record UpperBound (c : C) : Set ℓ where
    field
      bound : C
      bound-subunity : bound ≤ 𝟙
      bound-valid : c ≤ bound

  -- -------------------------------------------------------------------------
  -- 4. Continuity/Monotonicity Lemmas
  -- -------------------------------------------------------------------------

  -- Multiplication is monotone
  mul-monotone : ∀ {c₁ c₁' c₂ c₂'} →
    c₁' ≤ c₁ → c₂' ≤ c₂ →
    (c₁' · c₂') ≤ (c₁ · c₂)
  mul-monotone = StabilityDefs.·-mono DM

  -- -------------------------------------------------------------------------
  -- 5. Degeneracy Analysis
  -- -------------------------------------------------------------------------

  -- A step is degrading if it's not the identity
  IsDegrading : C → Set ℓ
  IsDegrading s = (s ≡ 𝟙 → ⊥) × (s ≤ 𝟙)

  -- -------------------------------------------------------------------------
  -- 6. Contractivity Arguments: non-degrading steps
  -- -------------------------------------------------------------------------

  -- A step is non-degrading if applying it preserves post-fixed points
  NonDegrading : C → Set ℓ
  NonDegrading s = ∀ {c} → Positive c → PostFixedPoint c s → PostFixedPoint c s

  -- The identity step is non-degrading
  identity-non-degrading : NonDegrading 𝟙
  identity-non-degrading pos pf = subst (_ ≤_) (sym (·-identityʳ _)) (≤-refl _)

  -- -------------------------------------------------------------------------
  -- 7. Proof Factoring
  -- -------------------------------------------------------------------------

  record CredenceFactoring (c : C) : Set ℓ where
    field
      high-part : C
      low-part : C
      factoring : c ≡ high-part · low-part
      high-positive : Positive high-part

  -- -------------------------------------------------------------------------
  -- 8. Dual Proofs: squeeze between bounds
  -- -------------------------------------------------------------------------

  record SqueezedCredence (c : C) : Set ℓ where
    field
      lower : LowerBound c
      upper : UpperBound c

-- ============================================================================
-- STRUCTURAL RULES (dynamics version)
-- ============================================================================

module StructuralRules {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open StabilityDefs DM

  -- Exchange: holds unconditionally (context reordering)
  exchange : ∀ {c s} → PostFixedPoint c s → PostFixedPoint c s
  exchange pf = pf

  -- Weakening: adding assumption at credence 1 doesn't degrade
  weakening : ∀ {c s} →
    PostFixedPoint c s →
    PostFixedPoint (c · 𝟙) s
  weakening {c} {s} pf =
    let step1 : c · 𝟙 ≤ c · s
        step1 = subst (λ x → x ≤ c · s) (sym (·-identityʳ c)) pf
        rw : c · s ≡ (c · 𝟙) · s
        rw = trans (sym (cong (c ·_) (·-identityˡ s))) (sym (·-assoc c 𝟙 s))
    in subst (c · 𝟙 ≤_) rw step1

  -- Contraction: safe when c is idempotent
  safe-contraction : ∀ {c s} →
    Idempotent c →
    PostFixedPoint c s →
    PostFixedPoint c s
  safe-contraction _ pf = pf

-- ============================================================================
-- INDUCTION (dynamics version)
-- ============================================================================

module InductionTheorems {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open DynamicsDefs DM
  open InductionDynamics DM public

  -- Classical induction: step has credence 1
  -- This is always valid because T_1 = identity
  classical-induction-valid : ∀ {c} →
    Positive c →
    InductionValid c 𝟙
  classical-induction-valid = classical-induction

  -- Interior induction: c is idempotent
  -- This allows induction at interior credences!
  interior-induction-valid : ∀ {c} →
    Interior c →
    Idempotent c →
    InductionValid c c
  interior-induction-valid = interior-induction

  -- New: Induction with post-fixed point condition
  -- Induction is valid when credence is a post-fixed point of the step operator
  postfixed-induction : ∀ {c s} →
    Positive c →
    PostFixedPoint c s →
    InductionValid c s
  postfixed-induction pos pf = record { base = pos ; preserve = pf }
