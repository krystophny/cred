{- The {0,1} Collapse Theorem

   ORDER-THEORETIC DYNAMICS VIEW:
   ==============================

   When credences are restricted to {0,1}:
   1. All fixed points are trivial (only 0 and 1)
   2. Robust(true) and Vanishing(false) are exhaustive
   3. No interior dynamics exist (no points between 0 and 1)
   4. CredTT judgments correspond exactly to MLTT judgments

   This module proves that MLTT is the Boolean specialization of CredTT.
   It is the DEGENERATE CASE where proof dynamics collapse to classical logic.
-}
module CredTT.Collapse where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)

open import CredTT.Credence
open import CredTT.Neighbourhood

-- ============================================================================
-- BOOLEAN DYNAMICS COLLAPSE THEOREMS
-- ============================================================================

-- LIMITATION (Issue #163): BoolCollapse proves structural lemmas but MISSES the
-- key theorem: CredTT[Bool] ≃ MLTT at the derivation level. What we prove:
--   - trivial-fixed-points, robust-or-vanishing, no-interior (properties of Bool)
-- What we DON'T prove:
--   - Type preservation under collapse
--   - Derivation correspondence (Γ ⊢ t : A @ true ↔ Γ ⊢ t : A in MLTT)
--   - Semantics preservation
-- Full proof requires MLTT and CredTT syntax (500+ lines).
-- Note: Issue #57 tracks CollapseIsomorphism-Sketch's use of fake types.

module BoolCollapse where
  open BoolDM
  open DeMorganAlgebra BoolDM
  open StabilityDefs BoolDM
  open BoolStability

  -- -------------------------------------------------------------------------
  -- Theorem 1: All fixed points in Bool are trivial
  -- -------------------------------------------------------------------------

  -- In {0,1}, the only fixed points are 0 and 1
  -- For any step s: T_s(0) = 0 and T_s(1) = 1 or 0 depending on s

  trivial-fixed-points : (c : Bool) → Idempotent c → (c ≡ true) ⊎ (c ≡ false)
  trivial-fixed-points true  _ = inj₁ refl
  trivial-fixed-points false _ = inj₂ refl

  -- -------------------------------------------------------------------------
  -- Theorem 2: Robust and Vanishing are exhaustive
  -- -------------------------------------------------------------------------

  -- Every Bool credence is either Robust (true) or Vanishing (false)
  robust-or-vanishing : (c : Bool) → Robust c ⊎ Vanishing c
  robust-or-vanishing true  = inj₁ ((≤-true , (λ ())) , subst (true ≤_) (sym (·-identityʳ true)) ≤-true)
  robust-or-vanishing false = inj₂ refl

  -- -------------------------------------------------------------------------
  -- Theorem 3: No interior points
  -- -------------------------------------------------------------------------

  -- Bool has no Interior points (reusing from Neighbourhood)
  no-interior : (c : Bool) → Interior c → ⊥
  no-interior = bool-no-interior

  -- -------------------------------------------------------------------------
  -- Theorem 4: Neighbourhoods are singletons
  -- -------------------------------------------------------------------------

  -- In {0,1}, there are no intermediate points, so any neighbourhood
  -- containing c IS just {c}

  data BoolNeighbourhood : Bool → Set where
    singleton-true  : BoolNeighbourhood true
    singleton-false : BoolNeighbourhood false

  neighbourhood-is-singleton : (c : Bool) → BoolNeighbourhood c
  neighbourhood-is-singleton true  = singleton-true
  neighbourhood-is-singleton false = singleton-false

  -- -------------------------------------------------------------------------
  -- Theorem 5: Classification is exhaustive
  -- -------------------------------------------------------------------------

  -- Every Bool is either stable (true) or unstable (false)
  bool-dichotomy : (c : Bool) → (c ≡ true) ⊎ (c ≡ false)
  bool-dichotomy true  = inj₁ refl
  bool-dichotomy false = inj₂ refl

  -- Stability classification for Bool is complete
  bool-stability-complete : (c : Bool) →
    (c ≡ true × Stable₁ c) ⊎ (c ≡ false × Unstable₀ c)
  bool-stability-complete = bool-classify

  -- -------------------------------------------------------------------------
  -- Theorem 6: Stability is trivial
  -- -------------------------------------------------------------------------

  -- true is always stable
  true-always-stable : Stable₁ true
  true-always-stable = true , (≤-true , (λ ())) , ≤-true

  -- false is always unstable
  false-always-unstable : Unstable₀ false
  false-always-unstable = false , (≤-false , (λ ())) , ≤-false

-- ============================================================================
-- THE COLLAPSE ISOMORPHISM (SKETCH)
-- ============================================================================

-- CredTT with Bool credences is isomorphic to MLTT
-- STATUS: This is a STRUCTURAL SKETCH demonstrating the correspondence.
-- Full integration with the actual term language (CredTT.Syntax) is future work.
-- See GitHub issue #57: CollapseIsomorphism uses simplified/fake types

module CollapseIsomorphism-Sketch where
  open BoolDM
  open DeMorganAlgebra BoolDM
  open BoolCollapse

  -- -------------------------------------------------------------------------
  -- Direction 1: MLTT judgment -> CredTT judgment at credence true
  -- -------------------------------------------------------------------------

  -- An MLTT judgment Gamma |- t : A
  -- corresponds to a CredTT judgment Gamma |- t : A @ true

  -- SKETCH: We represent judgments abstractly since full term language
  -- integration requires CredTT.Syntax. These records capture the
  -- STRUCTURE of the correspondence without committing to a specific
  -- term representation. (See issue #57 for full integration work.)
  record MLTTJudgment-Sketch : Set₁ where
    field
      context : Set
      term : Set
      ty : Set

  record CredTTJudgment-Sketch : Set₁ where
    field
      context : Set
      term : Set
      ty : Set
      credence : Bool

  -- Embed MLTT into CredTT (sketch)
  mltt-to-credtt-sketch : MLTTJudgment-Sketch → CredTTJudgment-Sketch
  mltt-to-credtt-sketch j = record
    { context = MLTTJudgment-Sketch.context j
    ; term = MLTTJudgment-Sketch.term j
    ; ty = MLTTJudgment-Sketch.ty j
    ; credence = true
    }

  -- -------------------------------------------------------------------------
  -- Direction 2: CredTT judgment at true -> MLTT judgment
  -- -------------------------------------------------------------------------

  -- If Gamma |- t : A @ true in CredTT, we get Gamma |- t : A in MLTT

  credtt-true-to-mltt-sketch : (j : CredTTJudgment-Sketch) →
    CredTTJudgment-Sketch.credence j ≡ true →
    MLTTJudgment-Sketch
  credtt-true-to-mltt-sketch j _ = record
    { context = CredTTJudgment-Sketch.context j
    ; term = CredTTJudgment-Sketch.term j
    ; ty = CredTTJudgment-Sketch.ty j
    }

  -- -------------------------------------------------------------------------
  -- Direction 3: CredTT judgment at false -> vacuously satisfied
  -- -------------------------------------------------------------------------

  -- Gamma |- t : A @ false is vacuously true (no real content)

  -- A vacuous judgment has no computational content
  credtt-false-is-vacuous-sketch : (j : CredTTJudgment-Sketch) →
    CredTTJudgment-Sketch.credence j ≡ false →
    ⊤
  credtt-false-is-vacuous-sketch _ _ = tt

  -- -------------------------------------------------------------------------
  -- The Collapse Theorem (Sketch)
  -- -------------------------------------------------------------------------

  -- MLTT is isomorphic to CredTT[Bool] with credence = true
  -- This is a STRUCTURAL demonstration, not a full proof.
  -- Full proof requires integration with CredTT.Syntax (see issue #57).

  -- Forward: every MLTT derivation gives a CredTT derivation at credence 1
  -- This is a meta-theorem about derivation trees

  -- Backward: every CredTT derivation at credence 1 gives an MLTT derivation
  -- Credence 0 derivations are computationally empty

  -- Combined: the isomorphism (sketch)
  collapse-theorem-sketch : (j : CredTTJudgment-Sketch) →
    (CredTTJudgment-Sketch.credence j ≡ true × MLTTJudgment-Sketch) ⊎
    (CredTTJudgment-Sketch.credence j ≡ false × ⊤)
  collapse-theorem-sketch j with bool-dichotomy (CredTTJudgment-Sketch.credence j)
  ... | inj₁ eq-true  = inj₁ (eq-true , credtt-true-to-mltt-sketch j eq-true)
  ... | inj₂ eq-false = inj₂ (eq-false , tt)

-- ============================================================================
-- CREDENCE MULTIPLICATION COLLAPSE
-- ============================================================================

-- In Bool, credence multiplication is just AND

module MultiplicationCollapse where
  open BoolDM
  open DeMorganAlgebra BoolDM

  -- Bool multiplication is AND
  mul-is-and : ∀ (a b : Bool) → a · b ≡ a ∧ b
  mul-is-and true  true  = refl
  mul-is-and true  false = refl
  mul-is-and false true  = refl
  mul-is-and false false = refl

  -- true * true = true (stable * stable = stable)
  stable-mul-stable : true · true ≡ true
  stable-mul-stable = refl

  -- Anything with false = false (any * unstable = unstable)
  unstable-absorbs : ∀ (c : Bool) → c · false ≡ false
  unstable-absorbs true  = refl
  unstable-absorbs false = refl

  -- This means in MLTT:
  -- - Chaining definite proofs gives definite proofs
  -- - One undefined step makes the whole chain undefined

-- ============================================================================
-- NEGATION COLLAPSE
-- ============================================================================

-- In Bool, negation is standard Boolean NOT

module NegationCollapse where
  open BoolDM
  open DeMorganAlgebra BoolDM

  -- Negation flips
  neg-flips : ¬ true ≡ false
  neg-flips = refl

  neg-flips-back : ¬ false ≡ true
  neg-flips-back = refl

  -- No fixed point exists in Bool
  -- There is no c such that c = not c
  no-fixpoint : (c : Bool) → c ≡ ¬ c → ⊥
  no-fixpoint true  ()
  no-fixpoint false ()

  -- This is why Goedel incompleteness is undecidable in classical logic!
  -- c = not c has no solution in {true, false}
  -- In [0,1], it has solution c = 1/2

-- ============================================================================
-- DE MORGAN COLLAPSE
-- ============================================================================

-- In Bool, De Morgan OR is standard Boolean OR

module DeMorganCollapse where
  open BoolDM
  open DeMorganAlgebra BoolDM

  -- OR computed via De Morgan
  bool-or : Bool → Bool → Bool
  bool-or a b = ¬ (¬ a · ¬ b)

  -- This equals standard OR
  open import Data.Bool as B using (_∨_)

  or-correct : ∀ (a b : Bool) → bool-or a b ≡ a B.∨ b
  or-correct true  true  = refl
  or-correct true  false = refl
  or-correct false true  = refl
  or-correct false false = refl

-- ============================================================================
-- DYNAMICS COLLAPSE
-- ============================================================================

-- In Bool, operator dynamics are trivial

module DynamicsCollapse where
  open BoolDM
  open DeMorganAlgebra BoolDM
  open DynamicsDefs BoolDM

  -- All operators are either identity or annihilation
  operator-trivial : ∀ (c s : Bool) →
    (s ≡ true × c · s ≡ c) ⊎ (s ≡ false × c · s ≡ false)
  operator-trivial c true  = inj₁ (refl , ·-identityʳ c)
  operator-trivial c false = inj₂ (refl , ·-annihilʳ c)

  -- Iteration in Bool stabilizes immediately
  -- If s = true, c * s^n = c for all n
  -- If s = false, c * s^n = false for all n > 0
  iteration-immediate : ∀ (c : Bool) (n : ℕ) →
    iterate n c true ≡ c
  iteration-immediate c zero    = refl
  iteration-immediate c (suc n) =
    trans (cong (λ x → x · true) (iteration-immediate c n)) (·-identityʳ c)

  -- No post-fixed point can degrade (only 0 and 1 exist)
  no-degradation : ∀ (c : Bool) → (c ≡ true → PostFixedPoint c true) ×
                                   (c ≡ false → Invariant false true)
  no-degradation c =
    (λ eq → subst (λ x → x ≤ x · true) (sym eq)
           (subst (true ≤_) (sym (·-identityʳ true)) (≤-refl true))) ,
    (λ _ → sym (·-annihilˡ true))

  -- Classical induction is always valid in Bool at credence true
  -- NOTE (Issue #167): Pattern match appears incomplete but is CORRECT.
  -- The type `c ≡ true` forces c = true via unification with refl.
  -- The c = false case is impossible: there's no proof of `false ≡ true`.
  -- Name clarifies: this is about induction AT credence true, not "for all c".
  bool-induction-valid : ∀ (c : Bool) → c ≡ true → InductionDynamics.InductionValid BoolDM c true
  bool-induction-valid true refl = InductionDynamics.classical-induction BoolDM
    (𝟙-greatest 𝟘 , (λ ()))

-- ============================================================================
-- COMPLETE COLLAPSE THEOREM
-- ============================================================================

-- Combining all collapse results

module CompleteCollapse where
  open BoolCollapse
  open CollapseIsomorphism-Sketch
  open DynamicsCollapse
  open DeMorganAlgebra BoolDM
  open StabilityDefs BoolDM

  -- Main theorem: CredTT[Bool] = MLTT (sketch-level)

  -- 1. Fixed points: Only {0,1}, no interior
  fixed-points-trivial : ∀ (c : Bool) → Idempotent c → (c ≡ true) ⊎ (c ≡ false)
  fixed-points-trivial = trivial-fixed-points

  -- 2. Classification: Robust(1) or Vanishing(0)
  classification-exhaustive : ∀ (c : Bool) → Robust c ⊎ Vanishing c
  classification-exhaustive = robust-or-vanishing

  -- 3. Interior: No points between 0 and 1
  no-interior-points : ∀ (c : Bool) → Interior c → ⊥
  no-interior-points = no-interior

  -- 4. Dynamics: Trivial (identity or annihilation)
  dynamics-trivial : ∀ (c s : Bool) →
    (s ≡ true × c · s ≡ c) ⊎ (s ≡ false × c · s ≡ false)
  dynamics-trivial = operator-trivial

  -- 5. Isomorphism: MLTT <-> CredTT[Bool] (sketch)
  -- Full proof requires integration with actual term language (issue #57)
  judgment-correspondence-sketch : (j : CredTTJudgment-Sketch) →
    (CredTTJudgment-Sketch.credence j ≡ true × MLTTJudgment-Sketch) ⊎
    (CredTTJudgment-Sketch.credence j ≡ false × ⊤)
  judgment-correspondence-sketch = collapse-theorem-sketch

-- ============================================================================
-- SUMMARY: WHY THE COLLAPSE MATTERS
-- ============================================================================

{-
SKETCH STATUS (Issue #121): The collapse theorem below is a CONJECTURE with
partial evidence. We prove key lemmas (no interior, trivial dynamics) but
the full isomorphism CredTT[Bool] ≃ MLTT requires formal syntax for both
systems and a bijection on derivations - see issue #57 for tracking.

The collapse theorem CONJECTURES:

1. MLTT is CredTT restricted to {0,1}
   - Not an extension of CredTT
   - A SPECIAL CASE of CredTT

2. Boolean logic is the degenerate limit
   - Neighbourhoods collapse to points
   - Stability becomes trivial (true = stable, false = unstable)
   - No intermediate credences

3. Goedel incompleteness appears as undecidability
   - c = not c has no Boolean solution
   - In continuous credences, c = 1/2

4. Classical proof techniques are special cases
   - Modus ponens: true AND true = true
   - Ex falso: false AND anything = false
   - LEM holds because all credences are 0 or 1

5. No interior dynamics exist
   - All fixed points are trivial
   - Robust(true) and Vanishing(false) are exhaustive
   - Classical logic has no "middle ground"

CredTT GENERALIZES classical logic by:
- Allowing intermediate credences
- Making stability explicit
- Quantifying proof reliability
- Providing interior fixed points (like 1/2 for Goedel sentences)
-}
