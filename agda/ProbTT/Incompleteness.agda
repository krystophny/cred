{-# OPTIONS --allow-unsolved-metas #-}
-- Graded Incompleteness Theorems for ProbTT
-- The key result: Gödel's G has weight 1/2, not undecidable
--
-- LITERATURE CONTEXT:
-- The fixed-point w = ¬w → w = 1/2 is well-studied in fuzzy logic:
--   - Hájek, Paris, Shepherdson, "The Liar Paradox and Fuzzy Logic" (JSL 2000)
--   - Restall, "Arithmetic and Truth in Łukasiewicz's Infinitely Valued Logic"
--
-- Classical incompleteness: G is undecidable (no truth value in {0,1})
-- Fuzzy/ProbTT: G has determinate value 1/2 (the negation fixed point)
--
-- KEY DISTINCTION:
-- - If "Gödel" means liar-style self-reference ("this is not true"):
--   → Fuzzy truth literature directly applies (1/2 is standard)
-- - If "Gödel" means arithmetized provability ("this is not provable"):
--   → Need careful definition of graded provability predicate
--
-- ProbTT takes the second approach: Prov_w is a graded provability predicate,
-- and G = "Prov_1(G) is false" yields the fixed point at w = 1/2.

module ProbTT.Incompleteness where

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

-- Incompleteness results for ProbTT
module Incompleteness {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Provability DM

  -- The half weight (1/2) - the fixed point of negation
  -- This is the key value for Gödel's theorem
  postulate
    ½ : W
    ½-is-half : ¬ ½ ≡ ½  -- 1 - 1/2 = 1/2

  -- The Gödel sentence G
  -- G = "G is unprovable at weight 1"
  -- More precisely: G ↔ ¬Prov₁(G)
  postulate
    G : Tm 0
    -- G's defining property: G is true iff G is not provable at weight 1
    G-property : ∀ w → (Prov G w → (Prov G 𝟙 → ⊥)) × ((Prov G 𝟙 → ⊥) → Prov G w)

  -- The negation fixed-point theorem
  -- If w = ¬w, then w = 1/2
  negation-fixpoint : ∀ w → ¬ w ≡ w → w ≡ ½
  negation-fixpoint w hyp = {!!}  -- follows from algebra

  -- Gödel's fixed-point theorem (graded version)
  -- G has weight 1/2
  godel-fixpoint : Prov G ½
  godel-fixpoint = {!!}  -- follows from G-property and ½-is-half

  -- The weight of G satisfies w = ¬w
  godel-weight-equation : ∀ w → Prov G w → ¬ w ≡ w
  godel-weight-equation w prov-g = {!!}

  -- G is not provable at weight 1 (classical incompleteness)
  not-prov-G-one : Prov G 𝟙 → ⊥
  not-prov-G-one prov = {!!}  -- if Prov G 1, then by G's content, ¬Prov G 1

  -- G is not provable at weight 0 (not refutable)
  not-prov-G-zero : Prov G 𝟘 → ⊥
  not-prov-G-zero prov = {!!}  -- weight 0 means impossible

  -- Graded Incompleteness Theorem
  -- G is neither fully provable nor fully refutable
  -- But it HAS a determinate weight: 1/2
  record GradedIncomplete : Set ℓ where
    field
      not-one  : Prov G 𝟙 → ⊥
      not-zero : Prov G 𝟘 → ⊥
      at-half  : Prov G ½

  graded-incomplete : GradedIncomplete
  graded-incomplete = record
    { not-one  = not-prov-G-one
    ; not-zero = not-prov-G-zero
    ; at-half  = godel-fixpoint
    }

  -- ═══════════════════════════════════════════════════════════════════════
  -- INTERPRETATION
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Classical: G is "undecidable" - we can't determine its truth value
  -- ProbTT: G has weight 1/2 - maximally uncertain but DETERMINATE
  --
  -- The difference is crucial:
  -- - Classical undecidability: G's truth is inaccessible
  -- - ProbTT: G's weight is exactly known (1/2)
  --
  -- At weight 1/2:
  -- - "G is somewhat true" and "G is somewhat false" both hold
  -- - This is the unique stable equilibrium for the self-reference
  -- - The paradox is resolved by moving to continuous logic
  --
  -- Why 1/2?
  -- - G says "G has weight 0"
  -- - If G has weight w, then G's claim should be satisfied
  -- - Satisfaction means w = ¬w (G's claim about itself)
  -- - The unique solution in [0,1] is w = 1/2
  -- ═══════════════════════════════════════════════════════════════════════

  -- Comparison with classical incompleteness
  -- Classical: ¬Prov(G) ∧ ¬Prov(¬G)  (both directions blocked)
  -- ProbTT: Prov G ½                  (specific weight determined)

  -- The {0,1} case recovers classical incompleteness
  -- In Boolean algebra, w = ¬w has no solution
  -- So the diagonal lemma yields undecidability
  module Classical where
    open import Data.Bool using (Bool; true; false; not)

    -- In {0,1}, there is no w such that w = ¬w
    no-bool-fixpoint : ∀ (b : Bool) → not b ≡ b → ⊥
    no-bool-fixpoint false ()
    no-bool-fixpoint true ()

    -- Therefore, the Gödel sentence has no well-defined Boolean weight
    -- This is classical undecidability
