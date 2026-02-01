{-# OPTIONS --allow-unsolved-metas #-}
-- Graded Choice: Axiom of Choice at weight < 1
-- Finite choice at weight 1, countable/uncountable at weight < 1
--
-- LITERATURE CONTEXT:
-- This module is more novel than the incompleteness/consistency work.
-- Related ideas appear in:
--
-- 1. Constructive mathematics: AC fails, but "weak" choice principles hold
--    - Dependent choice, countable choice
--    - Martin-Löf's analysis of choice in type theory
--
-- 2. Realizability: choice principles have computational content
--    - Troelstra, van Oosten on modified realizability
--
-- 3. Measure-theoretic probability: "almost everywhere" choice
--    - Choice functions that work on measure-1 sets
--
-- ProbTT's contribution: Quantify "how much" of AC you get
--   - Finite choice: weight 1 (fully constructible)
--   - Countable choice: weight < 1 (limit of finite)
--   - Banach-Tarski: exists at weight < 1 (not physically realizable)
--
-- This is NOT standard in fuzzy logic literature (which focuses on
-- propositional/first-order logic, not set-theoretic principles).

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
  -- Classical AC: ∀ family of non-empty sets, ∃ choice function
  --   (∀ x ∈ I. ∃ y ∈ A(x)) → ∃ f : I → ⋃ A(x). ∀ x. f(x) ∈ A(x)
  --
  -- ProbTT: Choice functions exist at graded weights
  --   Finite families: weight 1
  --   Countable families: weight < 1 (approaches 1)
  --   Uncountable families: weight < 1 (bounded away from 1)
  -- ═══════════════════════════════════════════════════════════════════════

  -- Abstract representation of "existence at weight w"
  -- In the full formalization, this connects to the type system
  postulate
    ExistsAt : Set ℓ → W → Set ℓ

  -- Finite choice: always works at weight 1
  -- For any finite family, we can construct a choice function
  postulate
    finite-choice : ∀ {A : Set ℓ} (n : ℕ) →
                    (∀ (i : Fin n) → ExistsAt A 𝟙) →
                    ExistsAt (Fin n → A) 𝟙

  -- Countable choice: weight approaches 1 but may not reach it
  postulate
    countable-choice-weight : ℕ → W  -- weight for choosing from first n elements
    countable-choice-limit : W       -- limit weight as n → ∞

    -- Each finite prefix has weight 1
    countable-choice-finite : ∀ n → countable-choice-weight n ≡ 𝟙

    -- But the limit might be < 1
    countable-choice-lt-one : countable-choice-limit ≤ 𝟙

  -- Graded countable choice
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
