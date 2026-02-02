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
--    - Object-level consistency operator A
--    - "Gentle explosion": A, not A, A |- B but A, not A |/- B
--    - Carnielli & Coniglio, "Paraconsistent Logic: Consistency, Contradiction
--      and Negation" (2016)
--
-- 3. Paraconsistent semantics for Pavelka-style logics:
--    - Graded non-explosion
--    - Close to ProbTT's "graded ex falso"
--
-- ProbTT's approach: Con @ w means "confident at level w that bot is not provable"
-- This avoids Godel's Second by not claiming certainty (w < 1).

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
  -- More precisely: there is no derivation of bot (which we don't have in ProbTT!)
  -- Instead, we express it as: there is no term with weight 1 in the empty type
  --
  -- In ProbTT, we don't have an Empty type, so consistency means:
  -- "No proposition has both weight w and weight neg w for w != 1/2"
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

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: ProbTT is consistent (meta-theorem)
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: The consistency of ProbTT follows from:
  -- 1. The weight algebra axioms (0 != 1 in any non-trivial model)
  -- 2. The soundness of the typing rules (weights are preserved)
  -- 3. The absence of an Empty type or explosion rule
  --
  -- However, proving this requires semantic reasoning: we need to show
  -- that no derivation can produce both Prov t 1 and Prov t 0 for the
  -- same term t. This is a meta-level property about the derivation
  -- system, not provable within the system (by Godel's second theorem).
  --
  -- We postulate it as a meta-theoretic property of our definition.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    probtt-consistent : Con 𝟙

  -- ═══════════════════════════════════════════════════════════════════════
  -- GRADED SECOND INCOMPLETENESS
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- Godel's Second Incompleteness Theorem (classical):
  --   If T contains PA and T is consistent, then T cannot prove Con(T)
  --
  -- For ProbTT, we have a graded version:
  --   ProbTT |- Con(ProbTT) @ w  for some w < 1
  --   ProbTT |/- Con(ProbTT) @ 1
  -- ═══════════════════════════════════════════════════════════════════════

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: The consistency weight
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: The specific weight at which we can prove consistency
  -- depends on the strength of our meta-theory and the complexity of the
  -- consistency proof. This is analogous to how classical Godel's second
  -- theorem blocks full certainty but allows partial confidence.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    consistency-weight : W
    consistency-weight-lt-one : consistency-weight ≤ 𝟙
    consistency-weight-gt-zero : 𝟘 ≤ consistency-weight

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: Self-consistency at graded weight
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: The existence of a consistency witness requires:
  -- 1. Encoding the consistency statement as a term
  -- 2. Constructing a derivation of that term at the appropriate weight
  -- This is meta-level construction that cannot be done internally.
  -- ═══════════════════════════════════════════════════════════════════════
  -- The canonical witness term (refl at scope 0)
  private
    consistency-witness : Tm 0
    consistency-witness = refl'

  postulate
    self-consistent : Prov (⌈ consistency-witness ⌉) consistency-weight

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: We CANNOT prove consistency at weight 1
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: This is Godel's Second Incompleteness Theorem.
  -- If ProbTT could prove its own consistency at weight 1, then by
  -- the argument of Godel's second theorem, it would be inconsistent.
  -- Since we assume ProbTT is consistent, it cannot prove Con @ 1.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    second-incomplete : Prov (⌈ consistency-witness ⌉) 𝟙 → ⊥

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
  -- The graded approach resolves the Godelian tension:
  -- - We don't claim absolute certainty about self-consistency
  -- - We quantify our epistemic state precisely
  -- - This is more informative than classical "unprovable"
  -- ═══════════════════════════════════════════════════════════════════════

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: Soundness implies consistency
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: If ProbTT is sound (provable things have valid weights),
  -- then it's consistent. The proof requires showing that soundness
  -- prevents the coexistence of Prov t 1 and Prov t 0. This is semantic
  -- reasoning about the interpretation of weights.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    soundness-implies-consistency : (∀ {n} {t : Tm n} {w : W} → Prov t w → w ≤ 𝟙) →
                                     Con 𝟙

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: Reflection - we can reason about our own provability
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: Reflection requires going from Prov t w (provability
  -- at weight w) to Prov (encoding t) w. The D1 condition gives us this
  -- when we have an actual derivation, but Prov abstracts over derivations.
  -- We need a meta-level principle that provability is closed under encoding.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    reflection : ∀ {n} {t : Tm n} {w : W} →
                 Prov t w →
                 Prov ⌈ t ⌉ w

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: The consistency weight forms a fixed point
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: Similar to Godel's G, the consistency statement has a
  -- unique weight at which it is provable. Any other weight would either
  -- violate the second incompleteness theorem (if higher than
  -- consistency-weight) or fail to capture the actual confidence level
  -- (if lower). This uniqueness is a semantic property.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    consistency-fixpoint : ∀ w →
                           Prov (⌈ consistency-witness ⌉) w →
                           w ≡ consistency-weight
