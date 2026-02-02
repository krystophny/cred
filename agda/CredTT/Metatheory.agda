-- Metatheory of CredTT: Subject Reduction and Progress
--
-- ISSUES #186, #187: Type Preservation and Progress Theorems
--
-- Subject Reduction (Type Preservation):
--   If Gamma |- t : A @ c and t --> t', then Gamma |- t' : A @ c' for some c'
--
-- Progress:
--   If . |- t : A @ c and c > 0, then either t is a value or t --> t' for some t'
--
-- Key insight: Credences do not affect reduction! Beta rules are purely syntactic.
-- Therefore:
-- 1. Subject reduction in CredTT follows MLTT pattern
-- 2. Progress must account for credence-0 terms (vacuously inhabited)

module CredTT.Metatheory where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃) renaming (_,_ to _P,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import CredTT.Credence
open import CredTT.Syntax
open import CredTT.Substitution
open import CredTT.Context
open import CredTT.Judgment
open import CredTT.Normalization

-- ============================================================================
-- SUBJECT REDUCTION (TYPE PRESERVATION) - Issue #186
-- ============================================================================
--
-- Theorem: If Gamma |- t : A @ c and t --> t', then there exists c'
-- such that Gamma |- t' : A @ c'.
--
-- PROOF STATUS: Theorem statement with postulated cases.
-- The structure follows standard MLTT proofs (substitution lemma + recursion).
-- ============================================================================

module SubjectReduction {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Normalization DM

  -- Value predicate: canonical forms
  data Value : ∀ {n} → Tm n → Set where
    val-lam  : ∀ {n} {A : Ty n} {t : Tm (suc n)} → Value (lam A t)
    val-pair : ∀ {n} {a b : Tm n} → Value a → Value b → Value (pair a b)
    val-inl  : ∀ {n} {a : Tm n} → Value a → Value (inl a)
    val-inr  : ∀ {n} {b : Tm n} → Value b → Value (inr b)
    val-refl : ∀ {n} → Value {n} refl'

  -- ========================================================================
  -- SUBJECT REDUCTION THEOREM (Issue #186)
  -- ========================================================================
  postulate
    subject-reduction : ∀ {n} {Γ : Ctx n} {t t' : Tm n} {A : Ty n} {c : C} →
      t ⟶ t' →
      Γ ⊢ t ∶ A 〔 c 〕 →
      ∃ λ c' → Γ ⊢ t' ∶ A 〔 c' 〕

-- ============================================================================
-- PROGRESS THEOREM - Issue #187
-- ============================================================================
--
-- Theorem: If . |- t : A @ c and c > 0, then either:
--   1. t is a value (canonical form), or
--   2. t --> t' for some t' (can take a step)
--
-- PROOF STATUS: Theorem statement with postulated cases.
-- The structure follows standard MLTT progress proofs.
-- ============================================================================

module Progress {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Normalization DM
  open SubjectReduction DM

  -- Positive credence: strictly greater than zero
  Positive : C → Set ℓ
  Positive c = (𝟘 ≤ c) × (𝟘 ≡ c → ⊥)

  -- ========================================================================
  -- PROGRESS THEOREM (Issue #187)
  -- ========================================================================
  -- The proof structure is:
  -- - Variable case: impossible in empty context
  -- - Lambda: already a value
  -- - Application: function must be lambda (canonical forms), can beta reduce
  -- - Pair: recursively check components
  -- - Projections: scrutinee must be pair, can beta reduce
  -- - Injections: recursively check payload
  -- - Case: scrutinee must be injection, can beta reduce
  -- - Refl: already a value
  -- - J: proof must be refl (canonical forms), can beta reduce
  --
  -- The canonical forms lemmas are postulated.
  -- ========================================================================
  postulate
    progress : ∀ {t : Tm 0} {A : Ty 0} {c : C} →
      ∅ ⊢ t ∶ A 〔 c 〕 →
      Positive c →
      Value t ⊎ (∃ λ t' → t ⟶ t')

  -- ========================================================================
  -- TYPE SAFETY: Combining Subject Reduction and Progress
  -- ========================================================================
  postulate
    type-safety : ∀ {t t' : Tm 0} {A : Ty 0} {c : C} →
      ∅ ⊢ t ∶ A 〔 c 〕 →
      Positive c →
      t ⟶* t' →
      Value t' ⊎ (∃ λ t'' → t' ⟶ t'')

  -- ========================================================================
  -- ZERO-CREDENCE TERMS: No Progress Required
  -- ========================================================================
  -- Terms at credence 0 represent vacuous or impossible propositions.
  -- They need not make progress because they carry no computational content.
  --
  -- This is the key difference from MLTT:
  -- - MLTT: All well-typed closed terms are values or can step
  -- - CredTT: Only POSITIVE credence terms must make progress
  -- ========================================================================
  zero-credence-no-progress : ∀ {t : Tm 0} {A : Ty 0} →
    ∅ ⊢ t ∶ A 〔 𝟘 〕 →
    ⊤
  zero-credence-no-progress _ = tt
