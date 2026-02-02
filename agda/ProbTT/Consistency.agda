-- Self-consistency of ProbTT at graded weight
--
-- STATUS: CONJECTURAL
-- This module presents AXIOMS about self-consistency, not proofs.
-- All core claims are POSTULATED.
--
-- WHAT THIS MODULE ACTUALLY SHOWS:
-- IF we assume ProbTT is consistent (meta-theorem),
-- AND we assume a consistency-weight parameter exists,
-- THEN we can state the graded second incompleteness conjecture.
--
-- This is a DEFINITION of what graded self-consistency would mean,
-- not a PROOF that ProbTT achieves it.
--
-- GODEL'S SECOND INCOMPLETENESS THEOREM:
-- A consistent system containing PA cannot prove its own consistency.
-- This applies to ProbTT as well - we cannot PROVE probtt-consistent
-- within ProbTT. We ASSUME it as a meta-theorem.
--
-- WHAT "GRADED CONSISTENCY" MEANS:
-- We conjecture that while ProbTT cannot prove Con @ 1 (full certainty),
-- it might prove Con @ w for some w < 1 (partial confidence).
-- The specific value of consistency-weight is UNKNOWN and POSTULATED.
--
-- LITERATURE:
-- - da Costa's C-systems and LFIs analyze paraconsistent self-reference
-- - Pavelka's graded consistency degrees for fuzzy theories
-- - These PROVE their results; we only POSTULATE ours

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

module Consistency {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM
  open Provability DM

  -- Consistency predicate
  -- Con w means no term has both weight 1 and weight 0 (contradiction)
  Con : W → Set ℓ
  Con w = ∀ {n} {t : Tm n} → Prov t 𝟙 → Prov t 𝟘 → ⊥

  -- No explosion: weight 0 derivations cannot produce positive weights
  NoExplosion : Set ℓ
  NoExplosion = ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} →
                Γ ⊢ t ∶ A 〔 𝟘 〕 →
                ∀ w → w ≤ 𝟘

  -- Graded consistency witness
  GradedCon : W → Set ℓ
  GradedCon w = ∃ λ (witness : Tm 0) → Prov witness w × Con 𝟙

  -- =========================================================================
  -- AXIOM: ProbTT is consistent
  -- =========================================================================
  -- This is a META-THEOREM that we ASSUME, not prove.
  --
  -- By Godel's Second Incompleteness Theorem, if ProbTT is consistent,
  -- it cannot prove its own consistency at weight 1.
  -- We therefore cannot derive this internally.
  --
  -- Justification: We believe ProbTT is consistent because:
  -- 1. The weight algebra axioms are consistent (0 != 1)
  -- 2. The typing rules preserve weights soundly
  -- 3. There is no Empty type or explosion rule
  --
  -- But we have NOT proven this formally. A proper proof would require:
  -- - Constructing a model (e.g., in set theory with [0,1] weights)
  -- - Proving the model satisfies all ProbTT rules
  -- - Deriving consistency from the model existence
  -- =========================================================================
  postulate
    probtt-consistent : Con 𝟙

  -- =========================================================================
  -- AXIOM: The consistency weight
  -- =========================================================================
  -- We ASSUME there exists a weight at which consistency can be "proven".
  --
  -- IMPORTANT: The specific value is UNKNOWN. We do not claim to know
  -- what consistency-weight is. It could be:
  -- - 1/2 (by analogy with Godel sentence)
  -- - Some other value determined by the proof structure
  -- - Dependent on the meta-theory strength
  --
  -- This is NOT derived from any fixed-point equation.
  -- It is simply an assumed parameter of the theory.
  -- =========================================================================
  postulate
    consistency-weight : W
    consistency-weight-lt-one : consistency-weight ≤ 𝟙
    consistency-weight-gt-zero : 𝟘 ≤ consistency-weight

  -- A canonical witness term
  private
    consistency-witness : Tm 0
    consistency-witness = refl'

  -- =========================================================================
  -- AXIOM: Self-consistency at graded weight
  -- =========================================================================
  -- We ASSUME ProbTT can prove its consistency at consistency-weight.
  --
  -- HONEST STATEMENT: This is the claim, not a theorem.
  -- We are DEFINING what it would mean for ProbTT to have graded
  -- self-consistency, then ASSUMING it holds.
  --
  -- A proper proof would require:
  -- 1. Formalizing "Con(ProbTT)" as a term in ProbTT
  -- 2. Constructing a derivation of that term at consistency-weight
  -- 3. Showing the derivation is valid
  --
  -- We do none of this. The postulate does all the work.
  -- =========================================================================
  postulate
    self-consistent : Prov (⌈ consistency-witness ⌉) consistency-weight

  -- =========================================================================
  -- AXIOM: Cannot prove consistency at weight 1
  -- =========================================================================
  -- This is Godel's Second Incompleteness Theorem.
  --
  -- HONEST STATEMENT: We are postulating the theorem, not proving it.
  -- Proving Godel's Second for ProbTT would require:
  -- 1. Encoding ProbTT's derivation system in ProbTT
  -- 2. Constructing the Godel sentence for consistency
  -- 3. Showing that Prov(Con) @ 1 implies inconsistency
  --
  -- These are substantial technical achievements we do not have.
  -- =========================================================================
  postulate
    second-incomplete : Prov (⌈ consistency-witness ⌉) 𝟙 → ⊥

  -- =========================================================================
  -- INTERPRETATION (HONEST VERSION)
  -- =========================================================================
  --
  -- What we have NOT shown:
  -- - That ProbTT is actually consistent (we assume it)
  -- - That consistency-weight has any particular value (unknown)
  -- - That self-consistent is achievable (postulated)
  -- - That Godel's Second applies (postulated, not proven)
  --
  -- What we HAVE done:
  -- - Defined what graded self-consistency WOULD mean
  -- - Stated the conjecture that ProbTT might achieve it
  -- - Identified the gap between weight 1 (impossible by Godel)
  --   and lower weights (conjecturally achievable)
  --
  -- The philosophical value is in the FRAMEWORK:
  -- - Consistency as a graded notion, not binary
  -- - The Godelian barrier applies at weight 1
  -- - Lower weights might be accessible (conjecture)
  --
  -- This reframes the Godel phenomenon in graded terms,
  -- but does NOT "solve" or "avoid" Godel's theorems.
  -- =========================================================================

  -- =========================================================================
  -- AXIOM: Soundness implies consistency
  -- =========================================================================
  -- Semantic reasoning: if weights are sound, no contradiction arises.
  -- This requires a model construction we do not have.
  -- =========================================================================
  postulate
    soundness-implies-consistency : (∀ {n} {t : Tm n} {w : W} → Prov t w → w ≤ 𝟙) →
                                     Con 𝟙

  -- =========================================================================
  -- AXIOM: Reflection principle
  -- =========================================================================
  -- From Prov t w to Prov (encoding t) w.
  -- Requires the D1 derivability condition, which is also postulated.
  -- =========================================================================
  postulate
    reflection : ∀ {n} {t : Tm n} {w : W} →
                 Prov t w →
                 Prov ⌈ t ⌉ w

  -- =========================================================================
  -- AXIOM: Uniqueness of consistency weight
  -- =========================================================================
  -- The consistency statement has a unique provability degree.
  -- This is analogous to the Godel sentence having a unique weight,
  -- but we do not derive it from any fixed-point equation.
  -- =========================================================================
  postulate
    consistency-fixpoint : ∀ w →
                           Prov (⌈ consistency-witness ⌉) w →
                           w ≡ consistency-weight
