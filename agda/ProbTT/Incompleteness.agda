-- Graded Incompleteness for ProbTT
--
-- STATUS: CONJECTURAL
-- This module presents a FRAMEWORK for analyzing Godel-style incompleteness
-- in a graded setting. The core results are POSTULATED, not proven.
--
-- WHAT THIS MODULE ACTUALLY SHOWS:
-- IF we assume the existence of a Godel sentence G with certain properties,
-- AND we assume G's weight satisfies w = neg w,
-- THEN G has weight 1/2 (the unique negation fixed point).
--
-- This is a conditional result, not a construction.
--
-- CRITICAL DISTINCTION: PROVABILITY vs TRUTH
-- Godel's incompleteness theorem is about PROVABILITY, not truth:
-- - G is TRUE in the standard model of arithmetic
-- - G is NOT PROVABLE in PA (assuming consistency)
-- These are different claims. G's truth value is 1, not 1/2.
--
-- What ProbTT offers is GRADED PROVABILITY:
-- - Weight represents confidence in PROVABILITY, not truth
-- - G may have provability degree 1/2 (maximally uncertain provability)
-- - This does NOT mean G is "half true" - G is fully true in N
--
-- LITERATURE:
-- The w = neg w analysis comes from fuzzy logic (Hajek-Paris-Shepherdson 2000),
-- applied to the LIAR sentence ("this sentence is false"), not Godel's G.
-- The liar directly talks about its own truth value.
-- Godel's G talks about provability, so the connection requires care.
--
-- HONEST CONTRIBUTION:
-- This module explores what happens if we model provability as graded.
-- The philosophical value is in the framework, not in claims about Godel.

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

module Incompleteness {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Provability DM

  -- =========================================================================
  -- AXIOM: Negation Fixed Point
  -- =========================================================================
  -- We ASSUME the weight algebra contains a negation fixed point.
  -- In the Boolean algebra {0,1}, NO such point exists (see Classical below).
  -- In [0,1] with neg w = 1 - w, the unique solution is 1/2.
  --
  -- This is an ASSUMPTION about the richness of the weight algebra.
  -- =========================================================================
  postulate
    ½ : W
    ½-is-half : ¬ ½ ≡ ½

  -- =========================================================================
  -- AXIOM: Godel Sentence Existence
  -- =========================================================================
  -- We ASSUME a sentence G exists with the stated property.
  --
  -- HONEST STATEMENT: This postulate does all the heavy lifting.
  -- We are NOT constructing G via the diagonal lemma.
  -- We are ASSUMING G exists and has the desired properties.
  --
  -- The diagonal lemma (Provability.agda) is also postulated, so even
  -- if we appealed to it, we would not have a real construction.
  -- =========================================================================
  postulate
    G : Tm 0
    -- G's defining property: G encodes "G is not provable at weight 1"
    G-property : ∀ w → (Prov G w → (Prov G 𝟙 → ⊥)) × ((Prov G 𝟙 → ⊥) → Prov G w)

  -- =========================================================================
  -- AXIOM: Uniqueness of Negation Fixed Point
  -- =========================================================================
  -- In [0,1], uniqueness is arithmetic: 1 - w = w implies w = 1/2.
  -- In general De Morgan algebras, there may be multiple fixed points.
  -- We ASSUME uniqueness for our algebra.
  -- =========================================================================
  postulate
    negation-fixpoint-unique : ∀ w → ¬ w ≡ w → w ≡ ½

  -- G is not provable at weight 1
  -- PROOF: Genuine, using G-property.
  -- If Prov G 1, then by G-property (first projection), Prov G 1 implies
  -- (Prov G 1 -> bot). Applying to our assumption yields bot.
  not-prov-G-one : Prov G 𝟙 → ⊥
  not-prov-G-one prov-G-1 = proj₁ (G-property 𝟙) prov-G-1 prov-G-1

  -- G is provable at weight 1/2
  -- PROOF: Uses G-property (second projection).
  -- Since (Prov G 1 -> bot) holds, G-property gives us Prov G w for any w.
  --
  -- NOTE: This "works" because G-property is postulated to make it work!
  -- The real question is whether G-property itself can be established.
  godel-fixpoint : Prov G ½
  godel-fixpoint = proj₂ (G-property ½) not-prov-G-one

  -- =========================================================================
  -- AXIOM: G is not provable at weight 0
  -- =========================================================================
  -- Weight 0 represents impossibility. If G is provable at 1/2, it should
  -- not be provable at 0 (which would mean "impossible").
  -- This requires semantic reasoning we do not formalize.
  -- =========================================================================
  postulate
    not-prov-G-zero : Prov G 𝟘 → ⊥

  -- =========================================================================
  -- AXIOM: G's weight satisfies the negation fixed-point equation
  -- =========================================================================
  -- THIS IS THE KEY PHILOSOPHICAL ISSUE (see issue #18).
  --
  -- G says "G is not provable at weight 1". Why does this imply w = neg w?
  --
  -- In fuzzy logic for the LIAR ("this sentence is false"):
  -- - The liar's content directly references its own truth value
  -- - v(L) = neg v(L) follows from the sentence's meaning
  --
  -- For Godel's G ("this sentence is not provable"):
  -- - G references PROVABILITY, not truth value
  -- - Why would provability weight satisfy w = neg w?
  --
  -- POSSIBLE INTERPRETATIONS:
  -- 1. We conflate provability and truth (philosophically problematic)
  -- 2. We define a "graded provability" where the equation makes sense
  -- 3. We accept this as an axiom about how weights interact with self-reference
  --
  -- We take option 3: postulate without claiming derivation.
  -- =========================================================================
  postulate
    godel-weight-equation : ∀ w → Prov G w → ¬ w ≡ w

  -- Graded Incompleteness: a packaging of the results
  record GradedIncomplete : Set ℓ where
    field
      not-one  : Prov G 𝟙 → ⊥   -- G not provable at weight 1
      not-zero : Prov G 𝟘 → ⊥   -- G not provable at weight 0
      at-half  : Prov G ½        -- G provable at weight 1/2

  graded-incomplete : GradedIncomplete
  graded-incomplete = record
    { not-one  = not-prov-G-one
    ; not-zero = not-prov-G-zero
    ; at-half  = godel-fixpoint
    }

  -- =========================================================================
  -- INTERPRETATION (HONEST VERSION)
  -- =========================================================================
  --
  -- What we have NOT shown:
  -- - That Godel's G "has truth value 1/2" (G is true, not half-true)
  -- - That classical incompleteness is "resolved" (it still applies)
  -- - That the diagonal lemma produces G with the stated properties
  --
  -- What we HAVE shown (conditionally):
  -- - IF G exists with the postulated properties
  -- - AND weights form a rich enough De Morgan algebra
  -- - THEN G is provable at the negation fixed point 1/2
  --
  -- The philosophical contribution is the FRAMEWORK:
  -- - Provability as a graded judgment
  -- - Self-referential sentences have determinate provability degree
  -- - The degree is determined by fixed-point equations
  --
  -- This is different from classical incompleteness (binary provable/not)
  -- and offers a new perspective on the Godel phenomenon.
  -- =========================================================================

  -- The Boolean case: no negation fixed point exists
  -- This shows why graded logic differs from classical logic
  module Classical where
    open import Data.Bool using (Bool; true; false; not)

    -- In {0,1}, there is no w such that not w = w
    no-bool-fixpoint : ∀ (b : Bool) → not b ≡ b → ⊥
    no-bool-fixpoint false ()
    no-bool-fixpoint true ()

    -- Interpretation: In Boolean logic, the negation fixed-point equation
    -- has no solution, so self-referential sentences are "undecidable".
    -- In richer algebras (like [0,1]), solutions exist.
