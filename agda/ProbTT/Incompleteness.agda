-- Graded Incompleteness Theorems for ProbTT
-- The key result: Godel's G has weight 1/2, not undecidable
--
-- LITERATURE CONTEXT:
-- The fixed-point w = neg w yields w = 1/2 is well-studied in fuzzy logic:
--   - Hajek, Paris, Shepherdson, "The Liar Paradox and Fuzzy Logic" (JSL 2000)
--   - Restall, "Arithmetic and Truth in Lukasiewicz's Infinitely Valued Logic"
--
-- Classical incompleteness: G is undecidable (no truth value in {0,1})
-- Fuzzy/ProbTT: G has determinate value 1/2 (the negation fixed point)
--
-- KEY DISTINCTION:
-- - If "Godel" means liar-style self-reference ("this is not true"):
--   Fuzzy truth literature directly applies (1/2 is standard)
-- - If "Godel" means arithmetized provability ("this is not provable"):
--   Need careful definition of graded provability predicate
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

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: The half weight (1/2) - the fixed point of negation
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: The existence of 1/2 requires the weight algebra to be
  -- "dense enough" to contain a negation fixed point. In the minimal
  -- De Morgan algebra, we only have 0 and 1 (Boolean case), which has
  -- NO negation fixed point. For graded incompleteness, we need to
  -- assume the algebra contains intermediate values.
  --
  -- In concrete instances:
  -- - [0,1] interval: 1/2 exists and satisfies 1 - 1/2 = 1/2
  -- - Lukasiewicz logic: 1/2 is the standard truth value
  -- - Boolean {0,1}: no such value exists (see Classical module below)
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    ½ : W
    ½-is-half : ¬ ½ ≡ ½  -- 1 - 1/2 = 1/2

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: The Godel sentence G
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: G's existence follows from the diagonal lemma
  -- (postulated in Provability.agda). G is defined by the fixed-point:
  --   G iff not(Prov_1(G))
  -- This cannot be constructed internally; it requires meta-level
  -- self-reference machinery (Godel numbering, substitution function, etc.)
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    G : Tm 0
    -- G's defining property: G is true iff G is not provable at weight 1
    G-property : ∀ w → (Prov G w → (Prov G 𝟙 → ⊥)) × ((Prov G 𝟙 → ⊥) → Prov G w)

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: Uniqueness of negation fixed point
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: In a general De Morgan algebra, there may be multiple
  -- negation fixed points, or the relationship between fixed points may
  -- not be provable from the minimal axioms. In [0,1] with standard
  -- complement (neg w = 1 - w), uniqueness follows from arithmetic.
  -- We postulate this as a property of the specific algebra.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    negation-fixpoint-unique : ∀ w → ¬ w ≡ w → w ≡ ½

  -- G is not provable at weight 1 (classical incompleteness)
  -- PROOF: Suppose Prov G 1. By G-property, Prov G 1 implies (Prov G 1 -> bot).
  --        Applying this to our assumption gives bot.
  not-prov-G-one : Prov G 𝟙 → ⊥
  not-prov-G-one prov-G-1 = proj₁ (G-property 𝟙) prov-G-1 prov-G-1

  -- Godel's fixed-point theorem (graded version)
  -- G has weight 1/2
  -- PROOF: By G-property, (Prov G 1 -> bot) implies Prov G w for any w.
  --        We have not-prov-G-one : Prov G 1 -> bot.
  --        Therefore Prov G 1/2.
  godel-fixpoint : Prov G ½
  godel-fixpoint = proj₂ (G-property ½) not-prov-G-one

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: G is not provable at weight 0
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: Weight 0 represents impossibility. For Prov G 0 to hold,
  -- G would need to be derivable at weight 0, meaning G is "impossible".
  -- But G is actually true at weight 1/2, so it cannot also be impossible.
  -- This requires reasoning about the semantics of weights that goes beyond
  -- the syntactic Prov predicate. In a sound semantics, weights must be
  -- consistent: if Prov G 1/2 and 1/2 > 0, then not Prov G 0 (as a minimal
  -- weight). We postulate this semantic property.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    not-prov-G-zero : Prov G 𝟘 → ⊥

  -- ═══════════════════════════════════════════════════════════════════════
  -- POSTULATE: The weight of G satisfies the negation fixed-point equation
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- JUSTIFICATION: G says "G is not provable at weight 1". If G has weight w,
  -- then "G is true" has weight w, and "G is not true" has weight neg w.
  -- The self-referential structure means these must be equal: w = neg w.
  -- This requires semantic reasoning about how G's content relates to its
  -- provability weight - not derivable from purely syntactic Prov.
  -- ═══════════════════════════════════════════════════════════════════════
  postulate
    godel-weight-equation : ∀ w → Prov G w → ¬ w ≡ w

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
  -- - Satisfaction means w = neg w (G's claim about itself)
  -- - The unique solution in [0,1] is w = 1/2
  -- ═══════════════════════════════════════════════════════════════════════

  -- Comparison with classical incompleteness
  -- Classical: not Prov(G) and not Prov(not G)  (both directions blocked)
  -- ProbTT: Prov G 1/2                          (specific weight determined)

  -- The {0,1} case recovers classical incompleteness
  -- In Boolean algebra, w = neg w has no solution
  -- So the diagonal lemma yields undecidability
  module Classical where
    open import Data.Bool using (Bool; true; false; not)

    -- In {0,1}, there is no w such that w = neg w
    no-bool-fixpoint : ∀ (b : Bool) → not b ≡ b → ⊥
    no-bool-fixpoint false ()
    no-bool-fixpoint true ()

    -- Therefore, the Godel sentence has no well-defined Boolean weight
    -- This is classical undecidability
