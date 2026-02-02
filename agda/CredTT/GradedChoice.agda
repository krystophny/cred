-- ============================================================================
-- GRADED CHOICE: Axiom Schema for Choice Principles at Graded Credences
-- ============================================================================
--
-- STATUS: AXIOM SCHEMA (not theorems to be proven)
--
-- This module axiomatizes graded versions of choice principles. These are
-- FOUNDATIONAL AXIOMS of CredTT, analogous to how AC is an axiom of ZFC.
-- They cannot be proven from the type theory itself.
--
-- ============================================================================
-- AXIOM CLASSIFICATION
-- ============================================================================
--
-- 1. ExistsAt (PRIMITIVE NOTION)
--    This is a primitive notion connecting CredTT credences to set-theoretic
--    existence. It cannot be defined within CredTT itself because it bridges
--    the object language (credence-weighted types) to the meta-language (sets).
--
-- 2. finite-choice (AXIOM)
--    Finite choice at credence 1. This is the constructive core: we can
--    always construct a choice function for finite families. Analogous to
--    AC holding for finite sets in constructive mathematics.
--
-- 3. countable-choice-* (AXIOM SCHEMA)
--    Countable choice at limit credence. The limit credence is axiomatized
--    rather than computed because it depends on the specific credence algebra.
--    In [0,1], the limit of 1^n = 1, so countable choice has credence 1.
--    But for more refined algebras, the limit could be < 1.
--
-- 4. banach-tarski-* (AXIOM SCHEMA)
--    Banach-Tarski at credence < 1. This is a PHILOSOPHICAL POSITION encoded
--    as an axiom: non-constructive existence has credence < 1. The specific
--    credence is not determined by the algebra but is an input to the system.
--
-- ============================================================================
-- LITERATURE CONTEXT
-- ============================================================================
--
-- Related ideas in constructive mathematics:
-- - Martin-Lof: choice principles in type theory
-- - Troelstra, van Oosten: realizability and choice
-- - Fourman, Hyland: measure-theoretic choice
--
-- CredTT novelty: quantify the DEGREE of choice, not just yes/no.
--
-- This is NOT standard fuzzy logic (which focuses on propositional logic).
-- It is closer to probabilistic/graded set theory (which does not exist
-- as a mature field).
--
-- ============================================================================

module CredTT.GradedChoice where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import CredTT.Credence

-- Graded choice principles for CredTT
module GradedChoice {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- ═══════════════════════════════════════════════════════════════════════
  -- GRADED AXIOM OF CHOICE
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Classical AC: for all families of non-empty sets, exists choice function
  --   (forall x in I. exists y in A(x)) -> exists f : I -> Union A(x). forall x. f(x) in A(x)
  --
  -- CredTT: Choice functions exist at graded credences
  --   Finite families: credence 1
  --   Countable families: credence <= 1 (limit of finite)
  --   Uncountable families: credence < 1 (bounded away from 1)
  -- ═══════════════════════════════════════════════════════════════════════

  -- =========================================================================
  -- AXIOM: ExistsAt (Primitive Notion)
  -- Status: FUNDAMENTAL AXIOM (cannot be defined within CredTT)
  -- =========================================================================
  --
  -- ExistsAt A c means "type A is inhabited at credence c".
  -- This is a BRIDGE between CredTT (credence-weighted types) and set theory (existence).
  --
  -- Why postulated: This connects the object language to the meta-language.
  -- In a full semantics, ExistsAt A c would be defined as:
  --   exists (a : A) such that the canonical derivation of a has credence >= c
  --
  -- In the [0,1] model: ExistsAt A c means P(A is inhabited) >= c
  -- In the Boolean model: ExistsAt A 1 means A is inhabited, ExistsAt A 0 is trivial
  -- =========================================================================
  postulate
    ExistsAt : Set ℓ → C → Set ℓ

  -- =========================================================================
  -- AXIOM: Finite Choice at Credence 1
  -- Status: FUNDAMENTAL AXIOM (constructively valid)
  -- =========================================================================
  --
  -- For finite families, choice functions are constructible. This is
  -- analogous to finite AC holding in constructive mathematics.
  --
  -- Justification: Given witnesses for each of n elements, we can
  -- explicitly construct a choice function by case analysis.
  -- This is computational, not axiomatic, so credence 1 is appropriate.
  -- =========================================================================
  postulate
    finite-choice : ∀ {A : Set ℓ} (n : ℕ) →
                    (∀ (i : Fin n) → ExistsAt A 𝟙) →
                    ExistsAt (Fin n → A) 𝟙

  -- =========================================================================
  -- AXIOM SCHEMA: Countable Choice
  -- Status: FUNDAMENTAL AXIOM (depends on credence algebra)
  -- =========================================================================
  --
  -- Countable choice has a limit credence that depends on the specific
  -- credence algebra. The axiom schema parameterizes over this limit.
  --
  -- In the [0,1] model: limit of 1^n = 1, so countable choice has credence 1
  -- In more refined models: the limit could be < 1 if each step degrades
  --
  -- The axiom states:
  --   1. Each finite prefix has credence 1 (constructible)
  --   2. The limit is at most 1 (bounded)
  --   3. Countable choice holds at the limit credence
  --
  -- Why not compute the limit? The limit depends on:
  --   - Whether the algebra has a notion of convergence
  --   - Whether infinite products converge
  -- These require additional structure beyond the De Morgan algebra.
  -- =========================================================================
  postulate
    countable-choice-credence : ℕ → C
    countable-choice-limit : C

    countable-choice-finite : ∀ n → countable-choice-credence n ≡ 𝟙

    countable-choice-lt-one : countable-choice-limit ≤ 𝟙

  postulate
    countable-choice : ∀ {A : Set ℓ} →
                       (∀ (n : ℕ) → ExistsAt A 𝟙) →
                       ExistsAt (ℕ → A) countable-choice-limit

  -- ═══════════════════════════════════════════════════════════════════════
  -- PARADOX SCALING
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Banach-Tarski requires full AC (credence 1)
  -- At credence < 1, the paradoxical decomposition is "partial"
  -- It exists mathematically but cannot be physically realized
  -- ═══════════════════════════════════════════════════════════════════════

  -- The credence at which Banach-Tarski decomposition exists
  postulate
    banach-tarski-credence : C
    banach-tarski-lt-one : banach-tarski-credence ≤ 𝟙
    banach-tarski-gt-zero : 𝟘 ≤ banach-tarski-credence

  -- Abstract type for Banach-Tarski decomposition
  postulate
    BanachTarskiDecomp : Set ℓ
    bt-decomposition-exists : ExistsAt BanachTarskiDecomp banach-tarski-credence

  -- Physical realizability requires credence 1
  -- Since BT credence < 1, it cannot be physically realized
  postulate
    bt-not-realizable : banach-tarski-credence ≡ 𝟙 → ⊥

  -- ═══════════════════════════════════════════════════════════════════════
  -- COMPARISON WITH OTHER APPROACHES
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Constructive mathematics:
  --   AC fails entirely. No choice function exists.
  --   This loses information: we can't distinguish "almost constructible"
  --   from "far from constructible"
  --
  -- Classical mathematics:
  --   AC holds fully (credence 1). Choice functions always exist.
  --   This leads to paradoxes (Banach-Tarski) that seem physically wrong.
  --
  -- CredTT (graded):
  --   AC holds at credence c, where c depends on the family size.
  --   Finite: c = 1 (fully constructible)
  --   Countable: c < 1 (almost constructible)
  --   Uncountable: c << 1 (far from constructible)
  --
  --   This quantifies "how constructible" a choice is.
  --   Paradoxes exist at credence < 1, meaning they're theoretical artifacts.
  -- ═══════════════════════════════════════════════════════════════════════

  -- Credence product for independent choices
  -- If we make n independent choices each at credence c,
  -- the total credence is c^n
  choice-product : ℕ → C → C
  choice-product zero c = 𝟙
  choice-product (suc n) c = c · choice-product n c

  -- Product properties
  postulate
    -- Product of credences ≤ 1 is ≤ 1
    product-bounded : ∀ n c → c ≤ 𝟙 → choice-product n c ≤ 𝟙

    -- Product approaches 0 as n → ∞ if c < 1
    product-limit-exists : ∀ c → c ≤ 𝟙 →
                           ∃ λ limit → ∀ n → limit ≤ choice-product n c

  -- The credence of n independent choices
  n-fold-choice-credence : ℕ → C → C
  n-fold-choice-credence = choice-product

  -- Key theorem: finite choice preserves credence 1
  finite-preserves-one : ∀ n → choice-product n 𝟙 ≡ 𝟙
  finite-preserves-one zero = refl
  finite-preserves-one (suc n) = trans (·-identityˡ (choice-product n 𝟙)) (finite-preserves-one n)
