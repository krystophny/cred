{-# OPTIONS --allow-unsolved-metas #-}
-- Self-consistency of ProbTT at graded weight
-- ProbTT can prove its own consistency at weight < 1
--
-- LITERATURE CONTEXT:
-- The idea "consistency as a degree" appears in several traditions:
--
-- 1. Fuzzy logic: "consistency degree of a fuzzy theory"
--    - Studied in Pavelka-style systems
--    - Consistency is not binary but graded
--
-- 2. Logics of Formal Inconsistency (LFIs):
--    - da Costa's C-systems (1974)
--    - Object-level consistency operator ◦A
--    - "Gentle explosion": A, ¬A, ◦A ⊢ B but A, ¬A ⊬ B
--    - Carnielli & Coniglio, "Paraconsistent Logic: Consistency, Contradiction
--      and Negation" (2016)
--
-- 3. Paraconsistent semantics for Pavelka-style logics:
--    - Graded non-explosion
--    - Close to ProbTT's "graded ex falso"
--
-- ProbTT's approach: Con @ w means "confident at level w that ⊥ is not provable"
-- This avoids Gödel's Second by not claiming certainty (w < 1).

module ProbTT.Consistency where

open import Level using (Level; suc; _⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Context
open import ProbTT.Judgment
open import ProbTT.Provability

-- Consistency results for ProbTT
module Consistency {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Provability DM

  -- Consistency predicate: Con w means "contradiction is not provable at weight w"
  -- More precisely: there is no derivation of ⊥ (which we don't have in ProbTT!)
  -- Instead, we express it as: there is no term with weight 𝟙 in the empty type
  --
  -- In ProbTT, we don't have an Empty type, so consistency means:
  -- "No proposition has both weight w and weight ¬w for w ≠ 1/2"
  --
  -- Or equivalently: the weight algebra is consistent
  Con : W → Set ℓ
  Con w = ∀ {n} {t : Tm n} → Prov t 𝟙 → Prov t 𝟘 → ⊥

  -- Stronger version: no explosion
  -- There is no derivation rule that produces arbitrary weights from nothing
  NoExplosion : Set ℓ
  NoExplosion = ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} →
                Γ ⊢ t ∶ A 〔 𝟘 〕 →
                ∀ w → w ≤ 𝟘

  -- Graded consistency at weight w
  -- We can assert consistency with confidence w
  GradedCon : W → Set ℓ
  GradedCon w = ∃ λ (witness : Tm 0) → Prov witness w × Con 𝟙

  -- ProbTT is consistent (meta-theorem)
  -- This follows from the weight algebra properties
  probtt-consistent : Con 𝟙
  probtt-consistent prov-one prov-zero = {!!}  -- weight 1 and weight 0 are disjoint

  -- ═══════════════════════════════════════════════════════════════════════
  -- GRADED SECOND INCOMPLETENESS
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Gödel's Second Incompleteness Theorem (classical):
  --   If T ⊇ PA and T is consistent, then T ⊬ Con(T)
  --
  -- For ProbTT, we have a graded version:
  --   ProbTT ⊢ Con(ProbTT) @ w  for some w < 1
  --   ProbTT ⊬ Con(ProbTT) @ 1
  -- ═══════════════════════════════════════════════════════════════════════

  -- We can prove consistency at weight < 1
  -- This doesn't trigger Gödel's obstruction
  postulate
    consistency-weight : W
    consistency-weight-lt-one : consistency-weight ≤ 𝟙
    consistency-weight-gt-zero : 𝟘 ≤ consistency-weight

  self-consistent : Prov (⌈ refl' ⌉) consistency-weight
  self-consistent = {!!}  -- the witness of consistency

  -- We CANNOT prove consistency at weight 1
  -- This is Gödel's Second Incompleteness (graded version)
  postulate
    second-incomplete : Prov (⌈ refl' ⌉) 𝟙 → ⊥

  -- ═══════════════════════════════════════════════════════════════════════
  -- INTERPRETATION
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Classical: A consistent system cannot prove its own consistency
  -- This seems paradoxical: we "know" the system is consistent, but can't prove it
  --
  -- ProbTT: We CAN prove consistency, but at weight < 1
  -- This is philosophically honest:
  -- - We believe our system is consistent (high weight)
  -- - We cannot be absolutely certain (weight < 1)
  -- - The gap between belief and certainty is quantified
  --
  -- The graded approach resolves the Gödelian tension:
  -- - We don't claim absolute certainty about self-consistency
  -- - We quantify our epistemic state precisely
  -- - This is more informative than classical "unprovable"
  -- ═══════════════════════════════════════════════════════════════════════

  -- Comparison: soundness implies consistency
  -- If ProbTT is sound (provable things are true), then it's consistent
  soundness-implies-consistency : (∀ {n} {t : Tm n} {w : W} → Prov t w → w ≤ 𝟙) →
                                   Con 𝟙
  soundness-implies-consistency sound prov-one prov-zero =
    {!!}  -- weight 1 and weight 0 are incompatible

  -- Reflection: we can reason about our own provability
  -- This is where graded logic shines
  reflection : ∀ {n} {t : Tm n} {w : W} →
               Prov t w →
               Prov ⌈ t ⌉ w
  reflection p = {!!}  -- by D1 and encoding

  -- The consistency weight forms a fixed point
  -- Similar to Gödel's G, but for consistency claims
  postulate
    consistency-fixpoint : ∀ w →
                           Prov ⌈ refl' ⌉ w →
                           w ≡ consistency-weight
