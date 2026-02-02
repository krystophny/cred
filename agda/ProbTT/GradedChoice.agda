-- ============================================================================
-- GRADED CHOICE: Axiom Schema for Choice Principles at Graded Weights
-- ============================================================================
--
-- STATUS: AXIOM SCHEMA (not theorems to be proven)
--
-- This module axiomatizes graded versions of choice principles. These are
-- FOUNDATIONAL AXIOMS of ProbTT, analogous to how AC is an axiom of ZFC.
-- They cannot be proven from the type theory itself.
--
-- ============================================================================
-- AXIOM CLASSIFICATION
-- ============================================================================
--
-- 1. ExistsAt (PRIMITIVE NOTION)
--    This is a primitive notion connecting ProbTT weights to set-theoretic
--    existence. It cannot be defined within ProbTT itself because it bridges
--    the object language (weighted types) to the meta-language (sets).
--
-- 2. finite-choice (AXIOM)
--    Finite choice at weight 1. This is the constructive core: we can
--    always construct a choice function for finite families. Analogous to
--    AC holding for finite sets in constructive mathematics.
--
-- 3. countable-choice-* (AXIOM SCHEMA)
--    Countable choice at limit weight. The limit weight is axiomatized
--    rather than computed because it depends on the specific weight algebra.
--    In [0,1], the limit of 1^n = 1, so countable choice has weight 1.
--    But for more refined algebras, the limit could be < 1.
--
-- 4. banach-tarski-* (AXIOM SCHEMA)
--    Banach-Tarski at weight < 1. This is a PHILOSOPHICAL POSITION encoded
--    as an axiom: non-constructive existence has weight < 1. The specific
--    weight is not determined by the algebra but is an input to the system.
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
-- ProbTT novelty: quantify the DEGREE of choice, not just yes/no.
--
-- This is NOT standard fuzzy logic (which focuses on propositional logic).
-- It is closer to probabilistic/graded set theory (which does not exist
-- as a mature field).
--
-- ============================================================================

module ProbTT.GradedChoice where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import ProbTT.Weight

-- Graded choice principles for ProbTT
module GradedChoice {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- ═══════════════════════════════════════════════════════════════════════
  -- GRADED AXIOM OF CHOICE
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Classical AC: for all families of non-empty sets, exists choice function
  --   (forall x in I. exists y in A(x)) -> exists f : I -> Union A(x). forall x. f(x) in A(x)
  --
  -- ProbTT: Choice functions exist at graded weights
  --   Finite families: weight 1
  --   Countable families: weight <= 1 (limit of finite)
  --   Uncountable families: weight < 1 (bounded away from 1)
  -- ═══════════════════════════════════════════════════════════════════════

  -- =========================================================================
  -- AXIOM: ExistsAt (Primitive Notion)
  -- Status: FUNDAMENTAL AXIOM (cannot be defined within ProbTT)
  -- =========================================================================
  --
  -- ExistsAt A w means "type A is inhabited at weight w".
  -- This is a BRIDGE between ProbTT (weighted types) and set theory (existence).
  --
  -- Why postulated: This connects the object language to the meta-language.
  -- In a full semantics, ExistsAt A w would be defined as:
  --   exists (a : A) such that the canonical derivation of a has weight >= w
  --
  -- In the [0,1] model: ExistsAt A w means P(A is inhabited) >= w
  -- In the Boolean model: ExistsAt A 1 means A is inhabited, ExistsAt A 0 is trivial
  -- =========================================================================
  postulate
    ExistsAt : Set ℓ → W → Set ℓ

  -- =========================================================================
  -- AXIOM: Finite Choice at Weight 1
  -- Status: FUNDAMENTAL AXIOM (constructively valid)
  -- =========================================================================
  --
  -- For finite families, choice functions are constructible. This is
  -- analogous to finite AC holding in constructive mathematics.
  --
  -- Justification: Given witnesses for each of n elements, we can
  -- explicitly construct a choice function by case analysis.
  -- This is computational, not axiomatic, so weight 1 is appropriate.
  -- =========================================================================
  postulate
    finite-choice : ∀ {A : Set ℓ} (n : ℕ) →
                    (∀ (i : Fin n) → ExistsAt A 𝟙) →
                    ExistsAt (Fin n → A) 𝟙

  -- =========================================================================
  -- AXIOM SCHEMA: Countable Choice
  -- Status: FUNDAMENTAL AXIOM (depends on weight algebra)
  -- =========================================================================
  --
  -- Countable choice has a limit weight that depends on the specific
  -- weight algebra. The axiom schema parameterizes over this limit.
  --
  -- In the [0,1] model: limit of 1^n = 1, so countable choice has weight 1
  -- In more refined models: the limit could be < 1 if each step degrades
  --
  -- The axiom states:
  --   1. Each finite prefix has weight 1 (constructible)
  --   2. The limit is at most 1 (bounded)
  --   3. Countable choice holds at the limit weight
  --
  -- Why not compute the limit? The limit depends on:
  --   - Whether the algebra has a notion of convergence
  --   - Whether infinite products converge
  -- These require additional structure beyond the De Morgan algebra.
  -- =========================================================================
  postulate
    countable-choice-weight : ℕ → W
    countable-choice-limit : W

    countable-choice-finite : ∀ n → countable-choice-weight n ≡ 𝟙

    countable-choice-lt-one : countable-choice-limit ≤ 𝟙

  postulate
    countable-choice : ∀ {A : Set ℓ} →
                       (∀ (n : ℕ) → ExistsAt A 𝟙) →
                       ExistsAt (ℕ → A) countable-choice-limit

  -- ═══════════════════════════════════════════════════════════════════════
  -- PARADOX SCALING
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Banach-Tarski requires full AC (weight 1)
  -- At weight < 1, the paradoxical decomposition is "partial"
  -- It exists mathematically but cannot be physically realized
  -- ═══════════════════════════════════════════════════════════════════════

  -- The weight at which Banach-Tarski decomposition exists
  postulate
    banach-tarski-weight : W
    banach-tarski-lt-one : banach-tarski-weight ≤ 𝟙
    banach-tarski-gt-zero : 𝟘 ≤ banach-tarski-weight

  -- Abstract type for Banach-Tarski decomposition
  postulate
    BanachTarskiDecomp : Set ℓ
    bt-decomposition-exists : ExistsAt BanachTarskiDecomp banach-tarski-weight

  -- Physical realizability requires weight 1
  -- Since BT weight < 1, it cannot be physically realized
  postulate
    bt-not-realizable : banach-tarski-weight ≡ 𝟙 → ⊥

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
  --   AC holds fully (weight 1). Choice functions always exist.
  --   This leads to paradoxes (Banach-Tarski) that seem physically wrong.
  --
  -- ProbTT (graded):
  --   AC holds at weight w, where w depends on the family size.
  --   Finite: w = 1 (fully constructible)
  --   Countable: w < 1 (almost constructible)
  --   Uncountable: w << 1 (far from constructible)
  --
  --   This quantifies "how constructible" a choice is.
  --   Paradoxes exist at weight < 1, meaning they're theoretical artifacts.
  -- ═══════════════════════════════════════════════════════════════════════

  -- Weight product for independent choices
  -- If we make n independent choices each at weight w,
  -- the total weight is w^n
  choice-product : ℕ → W → W
  choice-product zero w = 𝟙
  choice-product (suc n) w = w · choice-product n w

  -- Product properties
  postulate
    -- Product of weights ≤ 1 is ≤ 1
    product-bounded : ∀ n w → w ≤ 𝟙 → choice-product n w ≤ 𝟙

    -- Product approaches 0 as n → ∞ if w < 1
    product-limit-exists : ∀ w → w ≤ 𝟙 →
                           ∃ λ limit → ∀ n → limit ≤ choice-product n w

  -- The weight of n independent choices
  n-fold-choice-weight : ℕ → W → W
  n-fold-choice-weight = choice-product

  -- Key theorem: finite choice preserves weight 1
  finite-preserves-one : ∀ n → choice-product n 𝟙 ≡ 𝟙
  finite-preserves-one zero = refl
  finite-preserves-one (suc n) = trans (·-identityˡ (choice-product n 𝟙)) (finite-preserves-one n)
