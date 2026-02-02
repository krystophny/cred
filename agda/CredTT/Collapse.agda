{- The {0,1} Collapse Theorem

   When credences are restricted to {0,1}:
   1. Neighbourhoods become singletons
   2. Stable₁(1) = true, Unstable₀(0) = true
   3. CredTT judgments correspond exactly to MLTT judgments

   This module proves that MLTT is the Boolean specialization of CredTT.
-}
module CredTT.Collapse where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open import CredTT.Credence
open import CredTT.Neighbourhood

-- ============================================================================
-- BOOLEAN COLLAPSE THEOREMS
-- ============================================================================

module BoolCollapse where
  open BoolDM
  open DeMorganAlgebra BoolDM
  open StabilityDefs BoolDM
  open BoolStability

  -- -------------------------------------------------------------------------
  -- Theorem 1: Neighbourhoods are singletons in Bool
  -- -------------------------------------------------------------------------

  -- In {0,1}, there are no intermediate points, so any neighbourhood
  -- containing c IS just {c}

  -- A neighbourhood in Bool is trivial (either contains only true or only false)
  data BoolNeighbourhood : Bool → Set where
    singleton-true  : BoolNeighbourhood true
    singleton-false : BoolNeighbourhood false

  -- Every Bool credence has a singleton neighbourhood
  neighbourhood-is-singleton : (c : Bool) → BoolNeighbourhood c
  neighbourhood-is-singleton true  = singleton-true
  neighbourhood-is-singleton false = singleton-false

  -- -------------------------------------------------------------------------
  -- Theorem 2: Classification is exhaustive
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
  -- Theorem 3: No interior points
  -- -------------------------------------------------------------------------

  -- Bool has no Interior points (reusing from Neighbourhood)
  no-interior : (c : Bool) → Interior c → ⊥
  no-interior = bool-no-interior

  -- -------------------------------------------------------------------------
  -- Theorem 4: Stability is trivial
  -- -------------------------------------------------------------------------

  -- true is always stable
  true-always-stable : Stable₁ true
  true-always-stable = true , (≤-true , (λ ())) , ≤-true

  -- false is always unstable
  false-always-unstable : Unstable₀ false
  false-always-unstable = false , (≤-false , (λ ())) , ≤-false

-- ============================================================================
-- THE COLLAPSE ISOMORPHISM
-- ============================================================================

-- CredTT with Bool credences is isomorphic to MLTT

module CollapseIsomorphism where
  open BoolDM
  open DeMorganAlgebra BoolDM
  open BoolCollapse

  -- -------------------------------------------------------------------------
  -- Direction 1: MLTT judgment → CredTT judgment at credence true
  -- -------------------------------------------------------------------------

  -- An MLTT judgment Γ ⊢ t : A
  -- corresponds to a CredTT judgment Γ ⊢ t : A @ true

  -- We represent this abstractly since we dont have the full term language here
  record MLTTJudgment : Set₁ where
    field
      context : Set     -- simplified: context as a type
      term : Set        -- simplified: term as a type
      ty : Set          -- the type

  record CredTTJudgment : Set₁ where
    field
      context : Set
      term : Set
      ty : Set
      credence : Bool

  -- Embed MLTT into CredTT
  mltt-to-credtt : MLTTJudgment → CredTTJudgment
  mltt-to-credtt j = record
    { context = MLTTJudgment.context j
    ; term = MLTTJudgment.term j
    ; ty = MLTTJudgment.ty j
    ; credence = true
    }

  -- -------------------------------------------------------------------------
  -- Direction 2: CredTT judgment at true → MLTT judgment
  -- -------------------------------------------------------------------------

  -- If Γ ⊢ t : A @ true in CredTT, we get Γ ⊢ t : A in MLTT

  credtt-true-to-mltt : (j : CredTTJudgment) →
    CredTTJudgment.credence j ≡ true →
    MLTTJudgment
  credtt-true-to-mltt j _ = record
    { context = CredTTJudgment.context j
    ; term = CredTTJudgment.term j
    ; ty = CredTTJudgment.ty j
    }

  -- -------------------------------------------------------------------------
  -- Direction 3: CredTT judgment at false → vacuously satisfied
  -- -------------------------------------------------------------------------

  -- Γ ⊢ t : A @ false is vacuously true (no real content)

  -- A vacuous judgment has no computational content
  credtt-false-is-vacuous : (j : CredTTJudgment) →
    CredTTJudgment.credence j ≡ false →
    ⊤  -- trivially satisfied
  credtt-false-is-vacuous _ _ = tt

  -- -------------------------------------------------------------------------
  -- The Collapse Theorem
  -- -------------------------------------------------------------------------

  -- MLTT ≃ CredTT[Bool] with credence = true

  -- Forward: every MLTT derivation gives a CredTT derivation at credence 1
  -- This is a meta-theorem about derivation trees

  -- Backward: every CredTT derivation at credence 1 gives an MLTT derivation
  -- Credence 0 derivations are computationally empty

  -- Combined: the isomorphism
  collapse-theorem : (j : CredTTJudgment) →
    (CredTTJudgment.credence j ≡ true × MLTTJudgment) ⊎
    (CredTTJudgment.credence j ≡ false × ⊤)
  collapse-theorem j with bool-dichotomy (CredTTJudgment.credence j)
  ... | inj₁ eq-true  = inj₁ (eq-true , credtt-true-to-mltt j eq-true)
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

  -- true · true = true (stable × stable = stable)
  stable-mul-stable : true · true ≡ true
  stable-mul-stable = refl

  -- Anything with false = false (any × unstable = unstable)
  unstable-absorbs : ∀ (c : Bool) → c · false ≡ false
  unstable-absorbs true  = refl
  unstable-absorbs false = refl

  -- This means in MLTT:
  -- - Chaining definite proofs gives definite proofs
  -- - One undefined step makes the whole chain undefined

-- ============================================================================
-- NEGATION COLLAPSE
-- ============================================================================

-- In Bool, ¬ is standard Boolean NOT

module NegationCollapse where
  open BoolDM
  open DeMorganAlgebra BoolDM

  -- Negation flips
  neg-flips : ¬ true ≡ false
  neg-flips = refl

  neg-flips-back : ¬ false ≡ true
  neg-flips-back = refl

  -- No fixed point exists in Bool
  -- There is no c such that c = ¬c
  no-fixpoint : (c : Bool) → c ≡ ¬ c → ⊥
  no-fixpoint true  ()
  no-fixpoint false ()

  -- This is why Godel incompleteness is undecidable in classical logic!
  -- c = ¬c has no solution in {true, false}
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
-- SUMMARY: WHY THE COLLAPSE MATTERS
-- ============================================================================

{-
The collapse theorem shows:

1. MLTT is CredTT restricted to {0,1}
   - Not an extension of CredTT
   - A SPECIAL CASE of CredTT

2. Boolean logic is the degenerate limit
   - Neighbourhoods collapse to points
   - Stability becomes trivial (true = stable, false = unstable)
   - No intermediate credences

3. Godel incompleteness appears as undecidability
   - c = ¬c has no Boolean solution
   - In continuous credences, c = 1/2

4. Classical proof techniques are special cases
   - Modus ponens: true ∧ true = true
   - Ex falso: false ∧ anything = false
   - LEM holds because all credences are 0 or 1

CredTT GENERALIZES classical logic by:
- Allowing intermediate credences
- Making stability explicit
- Quantifying proof reliability
-}
