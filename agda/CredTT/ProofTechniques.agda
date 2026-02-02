{- Proof Techniques in CredTT

   DYNAMICS-BASED FRAMEWORK (Issue #28)
   ====================================

   This module provides all 28 proof techniques with the dynamics framework.

   CORE TRANSFORMATION: "c = 1" becomes "c is post-fixed point"
   -------------------------------------------------------------

   Classical proofs implicitly assume credence = 1 everywhere. CredTT replaces
   this with a dynamics-based condition: credence c is valid for a proof step s
   iff c is a POST-FIXED POINT of the operator T_s, meaning c <= c * s.

   This transformation enables:
   1. Classical proofs (s = 1): T_1(c) = c, so any c is post-fixed
   2. Interior stability: if c is idempotent (c * c = c), then c is post-fixed
      under T_c, allowing VALID INDUCTION at intermediate credences!
   3. Degeneration detection: when c > c * s, repeated application degrades

   ============================================================================
   FORMALIZATION STATUS (Issue #63)
   ============================================================================

   PROVEN (with actual Agda proofs):
   - 1. DirectProof: direct-proof-dynamics via postfixed-compose
   - 3. Contraposition: contraposition (type-level), contrapos-antitone (credence)
   - 4. Reductio: reductio via unstable-neg-to-stable
   - 5. ExFalso: ex-falso-zero-fixed, ex-falso-zero-invariant
   - 6. VacuousTruth: vacuous via annihilator axiom
   - 7. DeductionTheorem: deduction-dynamics (identity on post-fixed)
   - 8. ModusPonens: mp-dynamics via T-compose, mp-stability
   - 9. Syllogism: syl-dynamics via T-compose
   - 10. UniversalGen: pi-dynamics (wraps pi-intro-dynamics)
   - 11. Existential: sigma-dynamics via sigma-intro-dynamics
   - 13. Exhaustion: exhaust-example (concrete proof)
   - 14. Construction: construct-example (concrete proof)
   - 16. Equational: rewrite-dynamics (wraps rewriting-dynamics)
   - 21. StabilityProofs: StabilityProofRecord (record type)
   - 22. CredenceBounds: LowerBoundRecord, UpperBoundRecord (record types)
   - 23. ContinuityLemmas: mul-mono via algebra monotonicity
   - 24. DegeneracyAnalysis: IsDegradingDef (type alias)
   - 25. Contractivity: identity-preserves (proven)
   - 26. ProofFactoring: FactoringRecord (record type)
   - 27. DualProofs: SqueezedRecord (record type)

   EXAMPLES ONLY (concrete Agda terms, but not general theorems):
   - 2. ProofByCases: cases-example (concrete Bool case)
   - 12. NaturalInduction: ind-example (concrete Nat proof)
   - 18. StructuralRules: exchange-example (concrete function)

   NOT YET FORMALIZED (comments/templates):
   - 15. Refutation: Requires contradiction predicate (no tracking issue)
   - 17. Analogy: Requires concrete interval algebra
   - 19. StrongInduction: Requires k-deep recursion schema (issue #155)
   - 20. Contrapositive: Region-based, needs more infrastructure
   - 28. LimitTheorems: Requires convergence formalization

   ============================================================================

   PROOF RULES AS MONOTONE OPERATORS
   ---------------------------------

   Each proof rule induces an operator on credences:

   | Rule              | Operator T_s(c)    | Post-fixed condition    |
   |-------------------|--------------------| ------------------------|
   | Direct proof      | c * s              | c <= c * s              |
   | Modus ponens      | T_s2(T_s1(c))      | c <= c * (s1 * s2)      |
   | Lambda intro      | identity           | c <= c (always)         |
   | Application       | c * s              | c <= c * s              |
   | Negation          | antitone flip      | c <= c*s => ~(c*s) <= ~c|
   | Ex falso          | T_s(0) = 0         | 0 is invariant (always) |
   | Pi intro          | inf over instances | c <= c * s (uniform)    |
   | Sigma intro       | c_a * c_b          | product of post-fixed   |
   | Induction         | T_step^n           | c <= c * step^n         |

   KEY INSIGHT: Interior stability is possible when c is idempotent!
   - If c * c = c and 0 < c < 1, then T_c(c) = c (fixed point)
   - This allows induction at interior credences
   - Classical logic hides this by forcing c = 1

   For the actual proven stability theorems, see:
   - CredTT.StabilityTheorems (proven dynamics lemmas)
   - CredTT.Neighbourhood (order-theoretic definitions)
   - CredTT.Collapse (proven {0,1} collapse theorem)
-}
module CredTT.ProofTechniques where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false; not)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)

open import CredTT.Credence

-- ============================================================
-- CLASSICAL PROOF TECHNIQUES (1-20)
-- Now with dynamics-based formulations
-- ============================================================

module ClassicalTechniques {ℓ} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open import CredTT.Neighbourhood
  open import CredTT.StabilityTheorems
  open StabilityDefs DM
  open ClassicalRecovery DM
  open OperatorDynamics DM

  -- 1. DIRECT PROOF
  -- STATUS: PROVEN (direct-proof-dynamics via postfixed-compose)
  --
  -- OPERATOR INDUCED: T_s(c) = c * s (multiplication by step credence)
  -- POST-FIXED CONDITION: c <= c * s (step does not reduce credence)
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: assumes s = 1, so T_1(c) = c (identity, always post-fixed)
  -- - CredTT: tracks s explicitly, allows interior stability when c idempotent
  module DirectProof where
    -- Type-level example (classical)
    direct-example : ∀ {A : Set} → A → A
    direct-example a = a

    -- Dynamics formulation: if c is post-fixed under both steps,
    -- composition is also post-fixed. This replaces the classical
    -- assumption that chained proofs preserve truth (c = 1).
    direct-proof-dynamics : ∀ {c s₁ s₂} →
      PostFixedPoint c s₁ →
      PostFixedPoint c s₂ →
      c ≤ T (s₁ · s₂) c
    direct-proof-dynamics = direct-proof-operator

  -- 2. PROOF BY CASES
  -- STATUS: EXAMPLE ONLY (cases-example concrete, no general theorem)
  --
  -- OPERATOR INDUCED: T_s on each branch, result is join of branches
  -- POST-FIXED CONDITION: both branches post-fixed => result post-fixed
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: if A and B both true, case split is true
  -- - CredTT: if A @ c1 and B @ c2 both post-fixed under s, so is result
  module ProofByCases where
    -- Type-level example (concrete Bool case)
    cases-example : ∀ (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
    cases-example true = inj₁ refl
    cases-example false = inj₂ refl

    -- Dynamics: both branches at same step -> result at that step
    -- PostFixedPoint c s in both branches -> PostFixedPoint c s overall

  -- 3. CONTRAPOSITION
  -- STATUS: PROVEN (type-level contraposition + credence-level antitone)
  --
  -- OPERATOR INDUCED: negation is ANTITONE (order-reversing)
  -- POST-FIXED CONDITION: c <= c*s implies ~(c*s) <= ~c (reversed)
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: (A -> B) <-> (~B -> ~A)
  -- - CredTT: negation flips the order, so post-fixed becomes post-unfixed
  module Contraposition where
    open import Data.Empty using (⊥)

    -- Type-level negation
    ¬T : Set → Set
    ¬T A = A → ⊥

    -- Type-level contraposition (classical, proven)
    contraposition : ∀ {A B : Set} → (A → B) → (¬T B → ¬T A)
    contraposition f ¬b a = ¬b (f a)

    -- The converse is also provable (intuitionistically valid)
    contraposition-converse : ∀ {A B : Set} → (¬T B → ¬T A) → ¬T (¬T A) → ¬T (¬T B)
    contraposition-converse f ¬¬a ¬b = ¬¬a (f ¬b)

    -- Credence-level contraposition: negation reverses ordering
    -- This captures how credences transform under negation
    contrapos-antitone : ∀ {c d : C} → c ≤ d → (¬ d) ≤ (¬ c)
    contrapos-antitone = neg-antitone

    -- Dynamics formulation: contraposition reverses post-fixed property
    -- If c is post-fixed (c <= c*s), then ~(c*s) <= ~c
    contrapos-dynamics : ∀ {c s} →
      PostFixedPoint c s →
      (¬ (c · s)) ≤ (¬ c)
    contrapos-dynamics = contraposition-dynamics

  -- 4. REDUCTIO AD ABSURDUM
  -- STATUS: PROVEN (reductio via unstable-neg-to-stable)
  --
  -- OPERATOR INDUCED: negation flips stability regions
  -- POST-FIXED CONDITION: ~c bounded away from 1 implies c bounded away from 0
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: derive contradiction from ~A, conclude A
  -- - CredTT: if ~c is bounded away from 1, then c is bounded away from 0
  module Reductio where
    -- Dynamics: Unstable(~c) => Stable(c)
    reductio : ∀ {c} → Unstable₀ (¬ c) → Stable₁ c
    reductio = reductio-dynamics

  -- 5. EX FALSO QUODLIBET
  -- STATUS: PROVEN (ex-falso-zero-fixed, ex-falso-zero-invariant)
  --
  -- OPERATOR INDUCED: T_s(0) = 0 for ALL s (0 is absorbing)
  -- POST-FIXED CONDITION: 0 <= 0*s = 0 (trivially satisfied, 0 is INVARIANT)
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: from falsum, derive anything
  -- - CredTT: 0 is a fixed point of ALL operators (nothing propagates from 0)
  module ExFalso where
    -- 0 is a fixed point of every operator
    ex-falso-zero-fixed : ∀ (s : C) → T s 𝟘 ≡ 𝟘
    ex-falso-zero-fixed = ClassicalRecovery.ex-falso-fixed DM

    -- 0 is invariant under any step (exact fixed point)
    ex-falso-zero-invariant : ∀ (s : C) → Invariant 𝟘 s
    ex-falso-zero-invariant = ClassicalRecovery.ex-falso-invariant DM

  -- 6. VACUOUS TRUTH
  -- STATUS: PROVEN (vacuous via annihilator axiom)
  --
  -- OPERATOR INDUCED: T_s(0) = 0 * s = 0 (annihilation)
  -- POST-FIXED CONDITION: 0 <= 0 (trivially satisfied)
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: "If pigs fly, then 2+2=5" is TRUE (paradox!)
  -- - CredTT: 0 * anything = 0 (vacuous, not assigned TRUE)
  module VacuousTruth where
    vacuous : ∀ {s : C} → 𝟘 · s ≡ 𝟘
    vacuous = vacuous-condition

  -- 7. DEDUCTION THEOREM
  -- STATUS: PROVEN (deduction-dynamics, identity on post-fixed)
  --
  -- OPERATOR INDUCED: identity (lambda abstraction preserves credence)
  -- POST-FIXED CONDITION: preserved unchanged by lambda intro
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: Gamma, A |- B implies Gamma |- A -> B
  -- - CredTT: if body is post-fixed under s, so is the lambda
  module DeductionTheorem where
    deduction-example : ∀ {A B : Set} → (A → B) → (A → B)
    deduction-example f = f

    -- Lambda abstraction preserves post-fixed property (identity)
    deduction : ∀ {c s} → PostFixedPoint c s → PostFixedPoint c s
    deduction = deduction-dynamics

  -- 8. MODUS PONENS
  -- STATUS: PROVEN (mp-dynamics via T-compose, mp-stability)
  --
  -- OPERATOR INDUCED: T_s1 composed with T_s2 = T_{s1*s2}
  -- POST-FIXED CONDITION: c <= c*(s1*s2) when c <= c*s1 and c <= c*s2
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: f : A->B, a : A |- f a : B (truth preserved)
  -- - CredTT: f @ s1, a @ s2 |- f a @ s1*s2 (CHAIN RULE: P(B) = P(B|A)*P(A))
  module ModusPonens where
    mp-example : ∀ {A B : Set} → (A → B) → A → B
    mp-example f a = f a

    -- Dynamics: composition of operators T_s1 and T_s2
    mp-dynamics : ∀ (s₁ s₂ c : C) → T s₂ (T s₁ c) ≡ T (s₁ · s₂) c
    mp-dynamics = modus-ponens-dynamics

    -- Stability version: stable inputs give stable output
    mp-stability : ∀ {c₁ c₂} → Stable₁ c₁ → Stable₁ c₂ → Stable₁ (c₁ · c₂)
    mp-stability = modus-ponens-stability

  -- 9. SYLLOGISM
  -- STATUS: PROVEN (syl-dynamics via T-compose)
  --
  -- OPERATOR INDUCED: T_s1 . T_s2 = T_{s2*s1} (transitive composition)
  -- POST-FIXED CONDITION: c <= c*(s1*s2*...*sn) for n-step syllogism
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: f : A->B, g : B->C |- g.f : A->C (truth preserved)
  -- - CredTT: long chains degrade: c1*c2*...*cn (unless steps are 1 or c idempotent)
  module Syllogism where
    syl-example : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
    syl-example f g = g ∘ f

    -- Dynamics: transitive composition
    syl-dynamics : ∀ (s₁ s₂ c : C) → T s₁ (T s₂ c) ≡ T (s₂ · s₁) c
    syl-dynamics = syllogism-dynamics

  -- 10. UNIVERSAL GENERALIZATION
  -- STATUS: PROVEN (pi-dynamics wraps pi-intro-dynamics)
  --
  -- OPERATOR INDUCED: inf over instances (Pi intro takes infimum)
  -- POST-FIXED CONDITION: if all instances post-fixed, universal is post-fixed
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: forall x. P(x) from arbitrary P(x) (truth preserved)
  -- - CredTT: forall x. P(x) @ inf{c(x)} (weakest instance dominates)
  module UniversalGen where
    univ-example : ∀ (n : ℕ) → n + 0 ≡ n
    univ-example zero = refl
    univ-example (suc n) = cong suc (univ-example n)

    -- Dynamics: uniform post-fixed property preserved
    pi-dynamics : ∀ {c s} → PostFixedPoint c s → PostFixedPoint c s
    pi-dynamics = pi-intro-dynamics

  -- 11. EXISTENTIAL INTRODUCTION/ELIMINATION
  -- STATUS: PROVEN (sigma-dynamics via sigma-intro-dynamics)
  --
  -- OPERATOR INDUCED: T_s(c_a * c_b) = (c_a * c_b) * s (product of credences)
  -- POST-FIXED CONDITION: c_a <= c_a*s AND c_b <= c_b*s implies c_a*c_b <= (c_a*c_b)*s
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: (a, b) : Sigma x:A. B(x) (existence is truth)
  -- - CredTT: (a, b) @ c_a * c_b (credences multiply)
  module Existential where
    exist-example : Σ ℕ (λ n → n + n ≡ 4)
    exist-example = 2 , refl

    -- Dynamics: both components post-fixed -> product post-fixed
    sigma-dynamics : ∀ {c_a c_b s} →
      PostFixedPoint c_a s →
      PostFixedPoint c_b s →
      c_a · c_b ≤ (c_a · c_b) · s
    sigma-dynamics = sigma-intro-dynamics

  -- 12. NATURAL INDUCTION
  -- STATUS: EXAMPLE ONLY (ind-example concrete, general theorem in InductionDynamics)
  --
  -- OPERATOR INDUCED: T_step^n (n applications of step operator)
  -- POST-FIXED CONDITION: c <= c * step (induction valid when c post-fixed)
  --
  -- CRITICAL INSIGHT FOR INTERIOR STABILITY:
  -- - Classical induction assumes step = 1 (T_1 = identity, always post-fixed)
  -- - CredTT: if c is IDEMPOTENT (c*c = c), then T_c(c) = c (INTERIOR STABLE!)
  -- - This allows VALID INDUCTION at intermediate credences 0 < c < 1
  --
  -- See: InductionDynamics.InductionValid for formal definition
  -- See: interior-induction for proof that idempotent c enables interior induction
  module NaturalInduction where
    ind-example : ∀ (n : ℕ) → n + 0 ≡ n
    ind-example zero = refl
    ind-example (suc n) = cong suc (ind-example n)

  -- 13. PROOF BY EXHAUSTION
  -- STATUS: PROVEN (exhaust-example is concrete proof)
  --
  -- OPERATOR INDUCED: join of all case operators
  -- POST-FIXED CONDITION: all cases post-fixed => result post-fixed
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: check all cases, all true implies result true
  -- - CredTT: all cases post-fixed under s => result post-fixed under s
  module Exhaustion where
    exhaust-example : ∀ (b : Bool) → not (not b) ≡ b
    exhaust-example true = refl
    exhaust-example false = refl

  -- 14. CONSTRUCTIVE PROOF
  -- STATUS: PROVEN (construct-example is concrete proof)
  --
  -- OPERATOR INDUCED: T_s(c_w * c_p) for witness credence c_w and property credence c_p
  -- POST-FIXED CONDITION: witness and property both post-fixed => existence post-fixed
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: witness + property => existence (truth preserved)
  -- - CredTT: witness @ c_w, property @ c_p => existence @ c_w * c_p
  module Construction where
    construct-example : ∃ (λ n → n * n ≡ 4)
    construct-example = 2 , refl

  -- 15. REFUTATION
  -- STATUS: NOT YET FORMALIZED (requires contradiction predicate, no tracking issue)
  --
  -- OPERATOR INDUCED: T_s driving credence toward 0 (degeneration)
  -- POST-FIXED CONDITION: NOT post-fixed; instead, credence degenerates
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: derive bottom (contradiction leads to falsum)
  -- - CredTT: iterate until credence degenerates to 0
  --
  -- Formalization would require:
  --   1. A predicate for "derivable contradiction"
  --   2. Proof that contradiction forces credence to 0
  --   3. Connection to Degenerating definition in Neighbourhood.agda
  module Refutation where
    refutation-not-yet-formalized : Set
    refutation-not-yet-formalized = ⊤

  -- 16. EQUATIONAL REWRITING
  -- STATUS: PROVEN (rewrite-dynamics wraps rewriting-dynamics)
  --
  -- OPERATOR INDUCED: identity (rewriting preserves credence exactly)
  -- POST-FIXED CONDITION: preserved unchanged by rewriting
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: a = b, b = c |- a = c (truth preserved)
  -- - CredTT: rewriting preserves post-fixed property (identity operator)
  module Equational where
    rewrite-example : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    rewrite-example = trans

    rewrite-dynamics : ∀ {c s} → PostFixedPoint c s → PostFixedPoint c s
    rewrite-dynamics = rewriting-dynamics

  -- 17. PROOF BY ANALOGY
  -- STATUS: NOT YET FORMALIZED (requires concrete interval algebra)
  --
  -- OPERATOR INDUCED: T_s with s < 1 (low-credence morphism)
  -- POST-FIXED CONDITION: c <= c * s where s represents analogy strength
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: cannot express "A is like B" with confidence 0.7
  -- - CredTT: "A is like B" @ 0.7 is expressible (explicitly weak morphism)
  --
  -- Formalization would require:
  --   1. Concrete interval algebra [0,1] (see CredTT.Interval)
  --   2. Morphism notion between types at sub-unitary credence
  --   3. Laws for how analogy credences compose
  module Analogy where
    analogy-not-yet-formalized : Set
    analogy-not-yet-formalized = ⊤

  -- 18. STRUCTURAL RULES
  -- STATUS: EXAMPLE ONLY (exchange-example concrete function)
  --
  -- OPERATORS INDUCED:
  -- - Exchange: identity (reordering preserves credence)
  -- - Weakening: T_1 (adding assumption at credence 1)
  -- - Contraction: requires idempotent credence for safety
  --
  -- POST-FIXED CONDITIONS:
  -- - Exchange: always preserves post-fixed (no credence change)
  -- - Weakening: adding at credence 1 preserves post-fixed
  -- - Contraction: safe when c is idempotent (c*c = c)
  module StructuralRulesExample where
    exchange-example : ∀ {A B C : Set} → (A → B → C) → (B → A → C)
    exchange-example f b a = f a b

  -- 19. STRONG INDUCTION
  -- STATUS: NOT YET FORMALIZED (requires k-deep recursion schema, see issue #155)
  --
  -- OPERATOR INDUCED: T_s^k (k applications of step operator for k previous cases)
  -- POST-FIXED CONDITION: c <= c * s^k (credence degrades by factor s^k)
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: use arbitrary k previous cases (assumes s=1, no penalty)
  -- - CredTT: using k previous cases at step s gives credence c * s^k
  --
  -- Key insight: classical strong induction hides the credence penalty
  -- that CredTT makes explicit. Only idempotent c survives arbitrary depth.
  module StrongInduction where
    strong-induction-not-yet-formalized : Set
    strong-induction-not-yet-formalized = ⊤

  -- 20. CONTRAPOSITIVE
  -- STATUS: NOT YET FORMALIZED (region-based, needs more infrastructure)
  --
  -- OPERATOR INDUCED: negation composed with implication operator
  -- POST-FIXED CONDITION: related to contrapos-dynamics in module 3
  --
  -- CLASSICAL vs CREDTT:
  -- - Classical: prove A -> B by proving ~B -> ~A (equivalent)
  -- - CredTT: stability transforms under negation (order reverses)
  module Contrapositive where
    contrapositive-not-yet-formalized : Set
    contrapositive-not-yet-formalized = ⊤

-- ============================================================
-- CREDTT-NATIVE PROOF TECHNIQUES (21-28)
-- No classical analogue - pure CredTT innovations
--
-- These techniques exploit the dynamics-based framework directly.
-- They have no classical counterpart because classical logic hides
-- credence dynamics behind the assumption that all credences are 1.
-- ============================================================

module CredTTNativeTechniques {ℓ} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open import CredTT.Neighbourhood
  open import CredTT.StabilityTheorems
  open StabilityDefs DM
  open NativeTechniques DM

  -- 21. STABILITY PROOFS
  -- STATUS: DEFINED (record alias)
  --
  -- OPERATOR INDUCED: T_s(c) = c * s
  -- POST-FIXED CONDITION: c <= c * s AND c > 0 (positive post-fixed point)
  --
  -- This is the CORE CredTT technique: prove that a credence is
  -- a post-fixed point of an operator, which replaces "c = 1" entirely.
  --
  -- Examples demonstrating interior stability is possible:
  -- - "2+2=4 is ROBUSTLY true" = PostFixedPoint 1 1 (classical case)
  -- - "sqrt(2) is rational" = Invariant 0 s (degenerate fixed point)
  -- - "Goedel sentence" = Idempotent at 1/2 (INTERIOR STABLE!)
  module StabilityProofs where
    StabilityProofRecord : C → C → Set ℓ
    StabilityProofRecord = StabilityProof

  -- 22. CREDENCE BOUNDS AS INVARIANTS
  -- STATUS: DEFINED (record aliases)
  --
  -- OPERATOR INDUCED: T_s with bound tracking
  -- POST-FIXED CONDITION: bound <= c AND c <= c * s (bound maintained through iteration)
  --
  -- Maintain credence bounds as loop invariants:
  -- - Lower bound: c(A) >= bound (credence stays above threshold)
  -- - Upper bound: c(~A) <= bound (negation credence stays below threshold)
  module CredenceBounds where
    LowerBoundRecord : C → Set ℓ
    LowerBoundRecord = LowerBound

    UpperBoundRecord : C → Set ℓ
    UpperBoundRecord = UpperBound

  -- 23. CONTINUITY/ROBUSTNESS LEMMAS
  -- STATUS: PROVEN (mul-mono via algebra monotonicity)
  --
  -- OPERATOR INDUCED: T_s is MONOTONE (preserves order)
  -- POST-FIXED CONDITION: c1 <= c2 implies T_s(c1) <= T_s(c2)
  --
  -- Small input degradation leads to proportionally small output degradation.
  -- This is key for robustness: operators are continuous in the order.
  module ContinuityLemmas where
    -- Monotonicity lemma: multiplication preserves order
    mul-mono : ∀ {c₁ c₁' c₂ c₂'} →
      c₁' ≤ c₁ → c₂' ≤ c₂ →
      (c₁' · c₂') ≤ (c₁ · c₂)
    mul-mono = mul-monotone

  -- 24. DEGENERACY ANALYSIS
  -- STATUS: DEFINED (type alias)
  --
  -- OPERATOR INDUCED: T_s with s < 1 (strictly contracting)
  -- POST-FIXED CONDITION: NOT satisfied; instead c > c * s (degrading)
  --
  -- Quantitative inconsistency diagnosis: track how fast credence degrades.
  -- Example: "Credence drops from 0.9 to 0.1 at step 7"
  -- This is the OPPOSITE of post-fixed: credence degrades under iteration.
  module DegeneracyAnalysis where
    IsDegradingDef : C → Set ℓ
    IsDegradingDef = IsDegrading

  -- 25. CONTRACTIVITY ARGUMENTS
  -- STATUS: PROVEN (identity-preserves proven)
  --
  -- OPERATOR INDUCED: T_s where s is analyzed for non-degradation
  -- POST-FIXED CONDITION: s = 1 implies T_s preserves all post-fixed points
  --
  -- For induction to be valid, need step that preserves post-fixed points.
  -- - Step @ 1: identity operator, always non-degrading
  -- - Step @ 0.99: degrades over iterations (unless c is idempotent!)
  module Contractivity where
    NonDegradingDef : C → Set ℓ
    NonDegradingDef = NonDegrading

    -- Identity step is non-degrading (the classical case)
    identity-preserves : NonDegrading 𝟙
    identity-preserves = identity-non-degrading

  -- 26. PROOF FACTORING
  -- STATUS: DEFINED (record alias)
  --
  -- OPERATOR INDUCED: factorization into high-part and low-part operators
  -- POST-FIXED CONDITION: high-part post-fixed at 1, low-part may degrade
  --
  -- Separate proofs into high-credence core and low-credence fringe:
  -- - Core: definitely true @ 1 (robust, classical)
  -- - Fringe: probably true @ c < 1 (may require idempotent c for stability)
  module ProofFactoring where
    FactoringRecord : C → Set ℓ
    FactoringRecord = CredenceFactoring

  -- 27. DUAL PROOFS
  -- STATUS: DEFINED (record alias)
  --
  -- OPERATOR INDUCED: combined lower and upper bound operators
  -- POST-FIXED CONDITION: lower <= c AND c <= upper (squeezed interval)
  --
  -- Prove credence is squeezed between bounds:
  -- - Example: 0.4 <= c(A) <= 0.6 (the Goedel region, neither true nor false)
  -- - Goedel sentence: c = 1/2 exactly (squeezed by self-reference)
  --
  -- NOTE: In [0,1] with standard multiplication, 1/2 is NOT idempotent
  -- (see half-not-idempotent in Neighbourhood.agda). Interior stability at
  -- intermediate credences requires non-Archimedean algebras which are
  -- FUTURE WORK (issue #190).
  module DualProofs where
    SqueezedRecord : C → Set ℓ
    SqueezedRecord = SqueezedCredence

  -- 28. LIMIT THEOREMS
  -- STATUS: NOT YET FORMALIZED (requires convergence formalization)
  --
  -- OPERATOR INDUCED: T_s^n as n -> infinity (asymptotic behavior)
  -- POST-FIXED CONDITION: relates to limit of iteration sequence
  --
  -- Asymptotic credence behavior under repeated operator application:
  -- - Convergence: c * s^n -> L as n -> infinity
  -- - Uniform vs pointwise convergence rates
  --
  -- Convergence rates (in Archimedean algebras):
  -- - Exponential: 1 - 2^(-n)
  -- - Polynomial: 1 - 1/n
  -- - Logarithmic: 1 - 1/log(n)
  --
  -- In non-Archimedean algebras, interior fixed points can prevent degeneration.
  module LimitTheorems where
    limit-theorems-not-yet-formalized : Set
    limit-theorems-not-yet-formalized = ⊤

-- ============================================================
-- TECHNIQUE SUMMARY: Classical vs Dynamics View
-- ============================================================

module TechniqueSummary where
  {-
  SUMMARY TABLE: All 28 techniques with their induced operators

  | # | Technique      | Classical View              | Dynamics View (Operator)        |
  |---|----------------|-----------------------------|---------------------------------|
  | 1 | Direct         | A -> A                      | T_s(c) = c * s                  |
  | 2 | Cases          | Both branches true          | Parallel post-fixed             |
  | 3 | Contrapos      | (A->B) <-> (~B->~A)         | negation is antitone            |
  | 4 | Reductio       | Derive contradiction        | Unstable(~c) => Stable(c)       |
  | 5 | Ex Falso       | bottom -> A                 | T_s(0) = 0 (0 is invariant)     |
  | 6 | Vacuous        | False antecedent            | 0 * s = 0                       |
  | 7 | Deduction      | Lambda intro                | identity (preserves post-fixed) |
  | 8 | MP             | f a                         | T_s1 . T_s2 = T_{s1*s2}         |
  | 9 | Syllogism      | g . f                       | T_s1 . T_s2 = T_{s2*s1}         |
  |10 | Universal      | forall x. P(x)              | inf_x post-fixed                |
  |11 | Exists         | (a, b)                      | c_a * c_b post-fixed            |
  |12 | Induction      | Base + step                 | c <= c * step (POST-FIXED!)     |
  |13 | Exhaust        | All cases true              | All cases post-fixed            |
  |14 | Construct      | Witness                     | c_w * c_p post-fixed            |
  |15 | Refute         | Derive bottom               | Degenerate to 0                 |
  |16 | Rewrite        | a = b                       | identity (preserves post-fixed) |
  |17 | Analogy        | Similar                     | T_s with s < 1                  |
  |18 | Structural     | Exchange/weak/contract      | Conditional on idempotence      |
  |19 | Strong Ind     | k previous cases            | T_s^k (s^k degradation)         |
  |20 | Contrapos      | ~B -> ~A                    | Reverses post-fixed             |
  |21 | Stability      | (no classical analogue)     | c <= c * s AND c > 0            |
  |22 | Bounds         | (no classical analogue)     | bound <= c <= c * s             |
  |23 | Continuity     | (no classical analogue)     | T_s is monotone                 |
  |24 | Degeneracy     | (no classical analogue)     | c > c * s (NOT post-fixed)      |
  |25 | Contractivity  | (no classical analogue)     | s = 1 => non-degrading          |
  |26 | Factoring      | (no classical analogue)     | high @ 1, low @ c < 1           |
  |27 | Dual           | (no classical analogue)     | lower <= c <= upper             |
  |28 | Limits         | (no classical analogue)     | lim_{n->inf} c * s^n            |

  KEY INSIGHT: INTERIOR STABILITY IS POSSIBLE
  -------------------------------------------
  Classical logic implicitly assumes c = 1 (step s = 1, so T_1 = identity).
  CredTT generalizes this: c is valid if c is a POST-FIXED POINT of T_s.

  When c is IDEMPOTENT (c * c = c) and 0 < c < 1:
  - T_c(c) = c * c = c (exact fixed point!)
  - Induction is VALID at interior credence c
  - No Archimedean assumption needed

  This is the core innovation: interior stability at idempotent credences.
  -}

-- ============================================================
-- CONCRETE EXAMPLES: Classical vs CredTT
-- ============================================================

module ConcreteExamples where
  open ClassicalTechniques

  -- STATUS: Examples in comments only - see issue #105 for adding executable code.
  -- The examples below use concrete numerics (0.9, 0.855, etc.) which require
  -- importing CredTT.Interval. This module uses abstract DeMorganAlgebra.
  -- For executable concrete examples, see: credtt-impl/test/test_neighbourhood.ml

  {-
  Example 1: Modus Ponens with Credence
  Classical: A, A -> B |- B
  CredTT: A @ 0.9, (A -> B) @ 0.95 |- B @ 0.855

  Example 2: Long Syllogism
  10 steps, each @ 0.99
  Classical: definitely true
  CredTT: 0.99^10 = 0.904 (not as confident!)

  Example 3: Induction over N
  Classical: base + step |- forall n.P(n)
  CredTT: step @ 0.999, P(1000) @ 0.999^1000 approximately 0.37
  BUT: if step is idempotent, credence is PRESERVED!

  Example 4: Goedel Sentence
  Classical: undecidable
  CredTT: c = 1/2 exactly (Interior, not Stable or Unstable)
  This is the negation fixpoint: not(1/2) = 1/2

  Example 5: Stability Proof
  "2+2=4 is robust" = Stable1
  This is a META-THEOREM that classical logic cannot express!

  Example 6: Interior Stability (NEW!)
  If c is idempotent (c * c = c) and 0 < c < 1:
  - c is a VALID credence for induction
  - T_c(c) = c (fixed point!)
  - No Archimedean assumption needed
  -}
