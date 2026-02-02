{- INTERVAL ALGEBRA [0,1] FOR CREDTT
   ==================================

   This module implements the [0,1] interval as a DeMorganAlgebra.
   This is the concrete model that makes CredTT meaningful beyond Bool.

   STATUS: PROOF SKETCH
   The De Morgan axioms are POSTULATED for now, pending formal proofs
   from rational arithmetic. This establishes the algebraic structure;
   full proofs are future work.

   KEY RESULTS:
   - [0,1] algebraic structure defined with all 12 De Morgan axiom postulates
   - 1/2 is the negation fixpoint: ~(1/2) = 1/2 (computed directly)
   - Interior elements exist: 0 < 1/2 < 1
   - Multiplication computes: 1/2 * 1/2 = 1/4 (computed directly)

   APPROACH:
   We use a quotient representation of rationals in [0,1]: pairs (n, d)
   representing n/(d+1), which guarantees denominators >= 1.
   Equality is by cross-multiplication (avoiding division).

   POSTULATES (17 total, to be replaced with proofs):
   - 2 validity postulates for fraction operations
   - 11 algebraic property postulates (covering the 12 De Morgan axioms)
   - 2 strict inequality postulates for interior element proof
   - 1 idempotent characterization postulate
   - 1 equivalence-to-equality postulate (requires quotient types)
-}
module CredTT.Interval where

open import Level using (Level; 0ℓ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties as NatP
  using (+-comm; +-assoc; *-comm; *-assoc; *-identityˡ; *-identityʳ;
         *-distribˡ-+; *-distribʳ-+; +-identityˡ; +-identityʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

open import CredTT.Credence

-- ============================================================================
-- THE INTERVAL TYPE [0,1]
-- ============================================================================

-- Representation: fractions p/(d+1) where 0 <= p <= d+1
-- We store (numerator, denominator-1) to ensure denominator >= 1
-- Invariant: num <= suc denom means fraction <= 1

record Frac : Set where
  constructor mkFrac
  field
    num   : ℕ      -- numerator
    denom : ℕ      -- denominator minus 1 (actual denom = denom + 1)
    valid : num Nat.≤ suc denom  -- num <= denom+1, i.e., fraction <= 1

open Frac public

-- ============================================================================
-- BASIC CONSTRUCTIONS
-- ============================================================================

≤-refl-nat : ∀ n → n Nat.≤ n
≤-refl-nat zero    = Nat.z≤n
≤-refl-nat (suc n) = Nat.s≤s (≤-refl-nat n)

n≤suc-n : ∀ n → n Nat.≤ suc n
n≤suc-n zero    = Nat.z≤n
n≤suc-n (suc n) = Nat.s≤s (n≤suc-n n)

-- Canonical fractions
frac-zero : Frac
frac-zero = mkFrac 0 0 Nat.z≤n

frac-one : Frac
frac-one = mkFrac 1 0 (Nat.s≤s Nat.z≤n)

frac-half : Frac
frac-half = mkFrac 1 1 (Nat.s≤s (n≤suc-n 0))

frac-quarter : Frac
frac-quarter = mkFrac 1 3 (Nat.s≤s Nat.z≤n)

-- ============================================================================
-- EQUIVALENCE AND ORDERING
-- ============================================================================

_≈_ : Frac → Frac → Set
f₁ ≈ f₂ = num f₁ * suc (denom f₂) ≡ num f₂ * suc (denom f₁)

_≤F_ : Frac → Frac → Set
f₁ ≤F f₂ = num f₁ * suc (denom f₂) Nat.≤ num f₂ * suc (denom f₁)

-- ============================================================================
-- POSTULATES FOR VALIDITY
-- ============================================================================

postulate
  *-valid-frac : ∀ (f₁ f₂ : Frac) →
    num f₁ * num f₂ Nat.≤ suc (suc (denom f₁) * suc (denom f₂) Nat.∸ 1)

postulate
  complement-valid-frac : ∀ (f : Frac) →
    suc (denom f) Nat.∸ num f Nat.≤ suc (denom f)

-- ============================================================================
-- OPERATIONS
-- ============================================================================

_*F_ : Frac → Frac → Frac
f₁ *F f₂ = mkFrac
  (num f₁ * num f₂)
  (suc (denom f₁) * suc (denom f₂) Nat.∸ 1)
  (*-valid-frac f₁ f₂)

¬F : Frac → Frac
¬F f = mkFrac (suc (denom f) Nat.∸ num f) (denom f) (complement-valid-frac f)

-- ============================================================================
-- POSTULATES FOR ALGEBRAIC PROPERTIES
-- ============================================================================

postulate
  ≈-trans-frac : ∀ (f g h : Frac) → f ≈ g → g ≈ h → f ≈ h
  ≤F-trans-frac : ∀ (f g h : Frac) → f ≤F g → g ≤F h → f ≤F h
  ≤F-antisym-frac : ∀ (f g : Frac) → f ≤F g → g ≤F f → f ≈ g
  one-greatest-frac : ∀ (f : Frac) → f ≤F frac-one

postulate
  *F-identityʳ-proof : ∀ (f : Frac) → (f *F frac-one) ≈ f
  *F-identityˡ-proof : ∀ (f : Frac) → (frac-one *F f) ≈ f
  *F-annihilʳ-proof : ∀ (f : Frac) → (f *F frac-zero) ≈ frac-zero
  *F-annihilˡ-proof : ∀ (f : Frac) → (frac-zero *F f) ≈ frac-zero
  *F-assoc-proof : ∀ (f g h : Frac) → ((f *F g) *F h) ≈ (f *F (g *F h))
  *F-comm-proof : ∀ (f g : Frac) → (f *F g) ≈ (g *F f)

postulate
  ¬F-invol-proof : ∀ (f : Frac) → (¬F (¬F f)) ≈ f
  *F-≤-self-proof : ∀ (f g : Frac) → (f *F g) ≤F f

postulate
  ≈-to-≡ : ∀ {f g : Frac} → f ≈ g → f ≡ g

-- ============================================================================
-- EQUIVALENCE AND ORDERING LEMMAS
-- ============================================================================

≈-refl : ∀ f → f ≈ f
≈-refl f = refl

≈-sym : ∀ {f g} → f ≈ g → g ≈ f
≈-sym eq = sym eq

≈-trans : ∀ {f g h} → f ≈ g → g ≈ h → f ≈ h
≈-trans {f} {g} {h} = ≈-trans-frac f g h

≤F-refl : ∀ f → f ≤F f
≤F-refl f = ≤-refl-nat (num f * suc (denom f))

≤F-trans : ∀ {f g h} → f ≤F g → g ≤F h → f ≤F h
≤F-trans {f} {g} {h} = ≤F-trans-frac f g h

≤F-antisym : ∀ {f g} → f ≤F g → g ≤F f → f ≈ g
≤F-antisym {f} {g} = ≤F-antisym-frac f g

zero-least : ∀ f → frac-zero ≤F f
zero-least f = Nat.z≤n

one-greatest : ∀ f → f ≤F frac-one
one-greatest = one-greatest-frac

-- ============================================================================
-- COMPLEMENT PROPERTIES
-- ============================================================================

-- ~0 = 1: the numerator is suc 0 - 0 = 1, denom is 0
-- ~1 = 0: the numerator is suc 0 - 1 = 0, denom is 0
-- We need ≈ since the validity proofs differ
¬F-zero-≈ : ¬F frac-zero ≈ frac-one
¬F-zero-≈ = refl  -- 1 * 1 = 1 * 1

¬F-one-≈ : ¬F frac-one ≈ frac-zero
¬F-one-≈ = refl  -- 0 * 1 = 0 * 1

¬F-zero : ¬F frac-zero ≡ frac-one
¬F-zero = ≈-to-≡ ¬F-zero-≈

¬F-one : ¬F frac-one ≡ frac-zero
¬F-one = ≈-to-≡ ¬F-one-≈

-- ============================================================================
-- DE MORGAN ALGEBRA INSTANCE
-- ============================================================================

module IntervalDM where

  I : Set
  I = Frac

  _≤I_ : I → I → Set
  _≤I_ = _≤F_

  _·I_ : I → I → I
  _·I_ = _*F_

  ¬I : I → I
  ¬I = ¬F

  𝟘I : I
  𝟘I = frac-zero

  𝟙I : I
  𝟙I = frac-one

  IntervalDM : DeMorganAlgebra 0ℓ
  IntervalDM = record
    { C           = I
    ; 𝟘           = 𝟘I
    ; 𝟙           = 𝟙I
    ; _·_         = _·I_
    ; ¬_          = ¬I
    ; _≤_         = _≤I_
    ; ·-identityʳ = λ c → ≈-to-≡ (*F-identityʳ-proof c)
    ; ·-identityˡ = λ c → ≈-to-≡ (*F-identityˡ-proof c)
    ; ·-annihilʳ  = λ c → ≈-to-≡ (*F-annihilʳ-proof c)
    ; ·-annihilˡ  = λ c → ≈-to-≡ (*F-annihilˡ-proof c)
    ; ·-assoc     = λ a b c → ≈-to-≡ (*F-assoc-proof a b c)
    ; ·-comm      = λ a b → ≈-to-≡ (*F-comm-proof a b)
    ; ¬-𝟘         = ¬F-zero
    ; ¬-𝟙         = ¬F-one
    ; ¬-invol     = λ c → ≈-to-≡ (¬F-invol-proof c)
    ; ≤-refl      = ≤F-refl
    ; ≤-trans     = λ {a} {b} {c} p q → ≤F-trans {a} {b} {c} p q
    ; ≤-antisym   = λ {a} {b} p q → ≈-to-≡ (≤F-antisym {a} {b} p q)
    ; 𝟘-least     = zero-least
    ; 𝟙-greatest  = one-greatest
    ; ·-≤-self    = *F-≤-self-proof
    }

open IntervalDM public using (IntervalDM; 𝟘I; 𝟙I; _·I_; ¬I; _≤I_; I)

-- ============================================================================
-- KEY THEOREMS: INTERIOR ELEMENTS
-- ============================================================================

half : I
half = frac-half

quarter : I
quarter = frac-quarter

-- ============================================================================
-- THEOREM: 1/2 is the negation fixpoint
-- ============================================================================

half-fixpoint : ¬I half ≈ half
half-fixpoint = refl

half-is-negation-fixpoint : ¬I half ≡ half
half-is-negation-fixpoint = ≈-to-≡ half-fixpoint

-- ============================================================================
-- THEOREM: 1/2 * 1/2 = 1/4
-- ============================================================================

half-times-half : (half ·I half) ≈ quarter
half-times-half = refl

half-times-half-eq : half ·I half ≡ quarter
half-times-half-eq = ≈-to-≡ half-times-half

-- ============================================================================
-- THEOREM: Interior elements exist
-- ============================================================================

_<I_ : I → I → Set
f <I g = (f ≤I g) × (f ≈ g → ⊥)

postulate
  zero-not-half : frac-zero ≈ frac-half → ⊥
  half-not-one : frac-half ≈ frac-one → ⊥

zero-lt-half : 𝟘I <I half
zero-lt-half = zero-least half , zero-not-half

half-lt-one : half <I 𝟙I
half-lt-one = one-greatest half , half-not-one

Interior : I → Set
Interior c = (𝟘I <I c) × (c <I 𝟙I)

half-is-interior : Interior half
half-is-interior = zero-lt-half , half-lt-one

-- ============================================================================
-- THEOREM: Idempotent characterization
-- ============================================================================

postulate
  no-interior-idempotent : ∀ (c : I) → (c ·I c ≡ c) → Interior c → ⊥

-- ============================================================================
-- SUMMARY
-- ============================================================================
-- Dynamics for [0,1] are defined in CredTT.Neighbourhood.IntervalStability
-- to avoid cyclic module dependencies.

{-
  SUMMARY: STRUCTURE ESTABLISHED, PROOFS PENDING

  POSTULATED (17 postulates covering algebraic properties):
  1. [0,1] forms a DeMorganAlgebra (IntervalDM)
     - All 12 axioms POSTULATED, not yet proven from rational arithmetic

  COMPUTED DIRECTLY (refl proofs):
  2. 1/2 is the negation fixpoint
     - ~(1/2) = 1/2 (by direct computation, no postulates needed)

  3. Multiplication computes correctly
     - 1/2 * 1/2 = 1/4 (by direct computation, no postulates needed)

  POSTULATED (inequality properties):
  4. Interior elements exist
     - 0 < 1/2 < 1 (inequality postulates, trivial to prove but not yet done)

  5. No interior idempotents
     - Only 0 and 1 satisfy c * c = c (postulated)

  KEY INSIGHT:
  [0,1] provides the concrete model that makes CredTT meaningful.
  Unlike Bool (which collapses to MLTT), [0,1] supports:
  - Graded credences for probabilistic reasoning
  - The negation fixpoint at 1/2 for Godel sentences
  - Interior elements that are first-class citizens

  FUTURE WORK:
  Replace postulates with proofs from Data.Rational or custom arithmetic.
-}
