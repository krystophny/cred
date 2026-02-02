-- Metatheory Theorem Statements for CredTT
--
-- This module contains FORMAL STATEMENTS of metatheoretic theorems.
-- The actual proofs are tracked in GitHub issues #186 and #187.
--
-- IMPORTANT: These are STATEMENTS, not proofs!
-- The postulates define the theorem signatures that need to be proven.
--
-- Subject Reduction (Type Preservation) - Issue #186:
--   If Gamma |- t : A @ c and t --> t', then Gamma |- t' : A @ c' for some c'
--
-- Progress - Issue #187:
--   If . |- t : A @ c and c > 0, then either t is a value or t --> t' for some t'
--
-- Key insight: Credences do not affect reduction! Beta rules are purely syntactic.
-- Therefore:
-- 1. Subject reduction in CredTT follows MLTT pattern
-- 2. Progress must account for credence-0 terms (vacuously inhabited)

module CredTT.Metatheory.Statements where

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
-- VALUE PREDICATE: Canonical Forms
-- ============================================================================

module Values {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Normalization DM

  data Value : ∀ {n} → Tm n → Set where
    val-lam  : ∀ {n} {A : Ty n} {t : Tm (suc n)} → Value (lam A t)
    val-pair : ∀ {n} {a b : Tm n} → Value a → Value b → Value (pair a b)
    val-inl  : ∀ {n} {a : Tm n} → Value a → Value (inl a)
    val-inr  : ∀ {n} {b : Tm n} → Value b → Value (inr b)
    val-refl : ∀ {n} → Value {n} refl'

-- ============================================================================
-- SUBJECT REDUCTION STATEMENT - Issue #186
-- ============================================================================
--
-- Theorem: If Gamma |- t : A @ c and t --> t', then there exists c'
-- such that Gamma |- t' : A @ c'.
--
-- STATUS: Statement only. Proof requires:
--   1. Substitution lemma (from CredTT.Substitution)
--   2. Case analysis on reduction rules
--   3. Structural induction on typing derivation
--
-- See GitHub issue #186 for proof work.
-- ============================================================================

module SubjectReductionStatement {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Normalization DM
  open Values DM

  -- THEOREM STATEMENT (proof deferred to issue #186)
  postulate
    subject-reduction : ∀ {n} {Γ : Ctx n} {t t' : Tm n} {A : Ty n} {c : C} →
      t ⟶ t' →
      Γ ⊢ t ∶ A 〔 c 〕 →
      ∃ λ c' → Γ ⊢ t' ∶ A 〔 c' 〕

-- ============================================================================
-- PROGRESS STATEMENT - Issue #187
-- ============================================================================
--
-- Theorem: If . |- t : A @ c and c > 0, then either:
--   1. t is a value (canonical form), or
--   2. t --> t' for some t' (can take a step)
--
-- STATUS: Statement only. Proof requires:
--   1. Canonical forms lemmas (e.g., functions are lambdas)
--   2. Case analysis on term structure
--   3. Inversion lemmas for typing
--
-- See GitHub issue #187 for proof work.
-- ============================================================================

module ProgressStatement {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Normalization DM
  open Values DM

  -- Positive credence: strictly greater than zero
  Positive : C → Set ℓ
  Positive c = (𝟘 ≤ c) × (𝟘 ≡ c → ⊥)

  -- THEOREM STATEMENT (proof deferred to issue #187)
  postulate
    progress : ∀ {t : Tm 0} {A : Ty 0} {c : C} →
      ∅ ⊢ t ∶ A 〔 c 〕 →
      Positive c →
      Value t ⊎ (∃ λ t' → t ⟶ t')

-- ============================================================================
-- TYPE SAFETY STATEMENT - Combining Subject Reduction and Progress
-- ============================================================================
--
-- Type safety follows from subject reduction and progress.
-- Once both theorems are proven, this follows directly.
--
-- STATUS: Statement only. Depends on issues #186 and #187.
-- ============================================================================

module TypeSafetyStatement {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Normalization DM
  open Values DM
  open ProgressStatement DM

  -- THEOREM STATEMENT (depends on subject-reduction and progress)
  postulate
    type-safety : ∀ {t t' : Tm 0} {A : Ty 0} {c : C} →
      ∅ ⊢ t ∶ A 〔 c 〕 →
      Positive c →
      t ⟶* t' →
      Value t' ⊎ (∃ λ t'' → t' ⟶ t'')

-- ============================================================================
-- ZERO-CREDENCE SEMANTICS
-- ============================================================================
--
-- Terms at credence 0 represent vacuous or impossible propositions.
-- They need not make progress because they carry no computational content.
--
-- This is the key difference from MLTT:
-- - MLTT: All well-typed closed terms are values or can step
-- - CredTT: Only POSITIVE credence terms must make progress
--
-- This is a PROVEN fact (trivially true).
-- ============================================================================

module ZeroCredence {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM

  -- Trivially true: zero-credence terms have no progress requirement
  zero-credence-no-progress : ∀ {t : Tm 0} {A : Ty 0} →
    ∅ ⊢ t ∶ A 〔 𝟘 〕 →
    ⊤
  zero-credence-no-progress _ = tt
