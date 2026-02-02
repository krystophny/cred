{- Proof Techniques in CredTT

   DYNAMICS-BASED FRAMEWORK
   ========================

   This module provides all 28 proof techniques with the dynamics framework.

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

   KEY INSIGHT: Proofs are MONOTONE OPERATORS on credences
   - Each proof step s induces operator T_s(c) = c * s
   - Stability is about FIXED POINTS of these operators
   - PostFixedPoint: c <= c * s (step doesn't reduce credence)
   - Invariant: c = c * s (exact fixed point)
   - Idempotent: c * c = c (self-stable, may be interior!)

   REPLACES "c = 1" WITH "c is post-fixed point":
   - Classical proofs assume step = 1 (identity operator)
   - CredTT allows interior stability when c is idempotent
   - The dynamics view unifies classical and graded techniques

   For the actual proven stability theorems, see:
   - CredTT.StabilityTheorems (proven dynamics lemmas)
   - CredTT.Neighbourhood (order-theoretic definitions)
   - CredTT.Collapse (proven {0,1} collapse theorem)

   Each technique shows WHY CredTT is more expressive than MLTT:
   Classical logic hides credence dynamics; CredTT exposes them.
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
  -- Track credence accumulation via multiplication
  -- DYNAMICS: Composition of operators T_s1 composed with T_s2 = T_{s1*s2}
  module DirectProof where
    -- In classical logic: A -> A (identity)
    -- In CredTT: A @ c -> A @ c with c tracked

    direct-example : ∀ {A : Set} → A → A
    direct-example a = a

    -- Credence: input @ c -> output @ c (preserved when step = 1)
    -- Dynamics: PostFixedPoint c 1 holds for any c

    -- Dynamics formulation: if c is post-fixed under both steps,
    -- composition is also post-fixed
    direct-proof-dynamics : ∀ {c s₁ s₂} →
      PostFixedPoint c s₁ →
      PostFixedPoint c s₂ →
      c ≤ T (s₁ · s₂) c
    direct-proof-dynamics = direct-proof-operator

  -- 2. PROOF BY CASES
  -- Each branch stable -> result stable
  -- DYNAMICS: Parallel branches preserve post-fixed points
  module ProofByCases where
    -- Example: case analysis on Bool
    cases-example : ∀ (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
    cases-example true = inj₁ refl
    cases-example false = inj₂ refl

    -- Dynamics: both branches at same step -> result at that step
    -- PostFixedPoint c s in both branches -> PostFixedPoint c s overall

  -- 3. CONTRAPOSITION
  -- DYNAMICS: Negation reverses order (antitone)
  module Contraposition where
    open import Data.Empty using (⊥)

    -- Type-level negation
    ¬T : Set → Set
    ¬T A = A → ⊥

    -- =========================================================================
    -- ACTUAL CONTRAPOSITION (Issue #65):
    -- Classical: (A → B) → (¬B → ¬A)
    -- This is a genuine proof, not a placeholder.
    -- =========================================================================
    contraposition : ∀ {A B : Set} → (A → B) → (¬T B → ¬T A)
    contraposition f ¬b a = ¬b (f a)

    -- The converse is also provable (intuitionistically valid)
    -- Note: ¬T (¬T A) means (A → ⊥) → ⊥
    contraposition-converse : ∀ {A B : Set} → (¬T B → ¬T A) → ¬T (¬T A) → ¬T (¬T B)
    contraposition-converse f ¬¬a ¬b = ¬¬a (f ¬b)

    -- =========================================================================
    -- CREDENCE-LEVEL CONTRAPOSITION:
    -- CredTT: if c ≤ d, then ¬d ≤ ¬c (order reversal)
    --
    -- This is about how credences transform under negation, not about
    -- type-level implication. Both are valid notions of "contraposition"
    -- but at different levels.
    -- =========================================================================
    contrapos-antitone : ∀ {c d : C} → c ≤ d → (¬ d) ≤ (¬ c)
    contrapos-antitone = neg-antitone

    -- Dynamics formulation: contraposition reverses post-fixed property
    contrapos-dynamics : ∀ {c s} →
      PostFixedPoint c s →
      (¬ (c · s)) ≤ (¬ c)
    contrapos-dynamics = contraposition-dynamics

    -- =========================================================================
    -- NOTE ON CREDENCE-ANNOTATED CONTRAPOSITION:
    -- True credence-annotated contraposition would require:
    --   (A → B) @ c → (¬B → ¬A) @ c'
    -- where c' depends on how credences transform through the derivation.
    --
    -- This requires the full credence-annotated judgment infrastructure
    -- (CredTT.Judgment), which is currently a postulated framework.
    -- The credence-level contrapos-antitone captures the key insight:
    -- negation reverses the credence ordering.
    -- =========================================================================

  -- 4. REDUCTIO AD ABSURDUM
  -- DYNAMICS: Unstable negation implies stable positive
  module Reductio where
    -- If not A is bounded away from 1, A is bounded away from 0
    -- Dynamics: Unstable(not c) => Stable(c)

    reductio : ∀ {c} → Unstable₀ (¬ c) → Stable₁ c
    reductio = reductio-dynamics

  -- 5. EX FALSO QUODLIBET
  -- DYNAMICS: 0 is invariant under ALL operators
  module ExFalso where
    -- Classical: bottom -> A
    -- CredTT: at c = 0, T_s(0) = 0 for any s

    -- 0 is a fixed point of every operator
    ex-falso-zero-fixed : ∀ (s : C) → T s 𝟘 ≡ 𝟘
    ex-falso-zero-fixed = ClassicalRecovery.ex-falso-fixed DM

    -- 0 is invariant under any step
    ex-falso-zero-invariant : ∀ (s : C) → Invariant 𝟘 s
    ex-falso-zero-invariant = ClassicalRecovery.ex-falso-invariant DM

  -- 6. VACUOUS TRUTH
  -- DYNAMICS: Near-zero antecedent -> unconstrained conditional
  module VacuousTruth where
    -- Classical: "If pigs fly, then 2+2=5" is TRUE
    -- CredTT: 0 * anything = 0 (vacuous, not TRUE)

    vacuous : ∀ {s : C} → 𝟘 · s ≡ 𝟘
    vacuous = vacuous-condition

  -- 7. DEDUCTION THEOREM
  -- DYNAMICS: Lambda abstraction preserves post-fixed property
  module DeductionTheorem where
    -- Classical: Gamma, A |- B implies Gamma |- A -> B
    -- CredTT: if body is post-fixed under s, so is lambda

    deduction-example : ∀ {A B : Set} → (A → B) → (A → B)
    deduction-example f = f

    deduction : ∀ {c s} → PostFixedPoint c s → PostFixedPoint c s
    deduction = deduction-dynamics

  -- 8. MODUS PONENS
  -- DYNAMICS: T_s1 composed with T_s2 = T_{s1*s2}
  module ModusPonens where
    -- f : A -> B @ s1, a : A @ s2 |- f a : B @ s1 * s2

    mp-example : ∀ {A B : Set} → (A → B) → A → B
    mp-example f a = f a

    -- This is the CHAIN RULE: P(B) = P(B|A) * P(A)
    -- Dynamics: composition of operators

    mp-dynamics : ∀ (s₁ s₂ c : C) → T s₂ (T s₁ c) ≡ T (s₁ · s₂) c
    mp-dynamics = modus-ponens-dynamics

    mp-stability : ∀ {c₁ c₂} → Stable₁ c₁ → Stable₁ c₂ → Stable₁ (c₁ · c₂)
    mp-stability = modus-ponens-stability

  -- 9. SYLLOGISM
  -- DYNAMICS: Transitive composition of operators
  module Syllogism where
    -- f : A -> B @ c1, g : B -> C @ c2 |- g composed with f : A -> C @ c1 * c2

    syl-example : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
    syl-example f g = g ∘ f

    -- Long chains degrade: c1 * c2 * ... * cn
    -- Unless all steps are 1 (classical) or c is idempotent (interior stable)

    syl-dynamics : ∀ (s₁ s₂ c : C) → T s₁ (T s₂ c) ≡ T (s₂ · s₁) c
    syl-dynamics = syllogism-dynamics

  -- 10. UNIVERSAL GENERALIZATION
  -- DYNAMICS: Credence is infimum over instances
  module UniversalGen where
    -- Classical: forall x. P(x) from arbitrary P(x)
    -- CredTT: forall x. P(x) @ inf{c(x)}

    univ-example : ∀ (n : ℕ) → n + 0 ≡ n
    univ-example zero = refl
    univ-example (suc n) = cong suc (univ-example n)

    -- If every instance is post-fixed, universal is post-fixed
    pi-dynamics : ∀ {c s} → PostFixedPoint c s → PostFixedPoint c s
    pi-dynamics = pi-intro-dynamics

  -- 11. EXISTENTIAL INTRODUCTION/ELIMINATION
  -- DYNAMICS: Credences multiply (witness * property)
  module Existential where
    -- (a, b) : Sigma x:A. B(x) @ c_a * c_b

    exist-example : Σ ℕ (λ n → n + n ≡ 4)
    exist-example = 2 , refl

    -- Dynamics: both components post-fixed -> product post-fixed
    sigma-dynamics : ∀ {c_a c_b s} →
      PostFixedPoint c_a s →
      PostFixedPoint c_b s →
      c_a · c_b ≤ (c_a · c_b) · s
    sigma-dynamics = sigma-intro-dynamics

  -- 12. NATURAL INDUCTION
  -- DYNAMICS: Valid iff c is post-fixed point of step operator
  module NaturalInduction where
    -- CRITICAL INSIGHT:
    -- Classical induction assumes step = 1 (T_1 = identity)
    -- Interior induction: if c is idempotent, T_c(c) = c

    ind-example : ∀ (n : ℕ) → n + 0 ≡ n
    ind-example zero = refl
    ind-example (suc n) = cong suc (ind-example n)

    -- Induction valid when: base is positive AND step is post-fixed
    -- See: InductionDynamics.InductionValid for formal definition

  -- 13. PROOF BY EXHAUSTION
  -- DYNAMICS: All cases post-fixed -> result post-fixed
  module Exhaustion where
    exhaust-example : ∀ (b : Bool) → not (not b) ≡ b
    exhaust-example true = refl
    exhaust-example false = refl

    -- 2 cases at step s -> result at step s

  -- 14. CONSTRUCTIVE PROOF
  -- DYNAMICS: Witness @ c, property @ d -> existence @ c * d
  module Construction where
    construct-example : ∃ (λ n → n * n ≡ 4)
    construct-example = 2 , refl

  -- 15. REFUTATION
  -- DYNAMICS: Drive credence to 0 (degeneration)
  -- STATUS: Not yet formalized (no tracking issue)
  module Refutation where
    -- Classical: derive bottom (contradiction leads to falsum)
    -- CredTT: iterate until credence degenerates to 0
    --
    -- Formalization would require:
    --   1. A predicate for "derivable contradiction"
    --   2. Proof that contradiction forces credence to 0
    --   3. Connection to Degenerating definition in Neighbourhood.agda
    --
    -- See: ClassicalRecovery.ex-falso-fixed for the 0-is-fixed-point property
    refutation-not-yet-formalized : Set
    refutation-not-yet-formalized = ⊤

  -- 16. EQUATIONAL REWRITING
  -- DYNAMICS: Preserves post-fixed property
  module Equational where
    rewrite-example : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    rewrite-example = trans

    rewrite-dynamics : ∀ {c s} → PostFixedPoint c s → PostFixedPoint c s
    rewrite-dynamics = rewriting-dynamics

  -- 17. PROOF BY ANALOGY
  -- DYNAMICS: Low-credence morphism (explicitly weak)
  -- STATUS: Not yet formalized (requires concrete credence algebra)
  module Analogy where
    -- "A is like B" @ 0.7 (explicitly weak)
    -- CredTT can express this; classical logic cannot
    --
    -- Formalization would require:
    --   1. Concrete interval algebra [0,1] (see CredTT.Interval)
    --   2. Morphism notion between types at sub-unitary credence
    --   3. Laws for how analogy credences compose
    --
    -- This is a conceptual technique - shows CredTT's expressiveness
    -- beyond classical logic, but precise formalization is future work.
    analogy-not-yet-formalized : Set
    analogy-not-yet-formalized = ⊤

  -- 18. STRUCTURAL RULES
  -- DYNAMICS: Exchange free, weakening/contraction conditional
  module StructuralRulesExample where
    exchange-example : ∀ {A B C : Set} → (A → B → C) → (B → A → C)
    exchange-example f b a = f a b

    -- Exchange: always preserves post-fixed
    -- Weakening: adding at credence 1 preserves post-fixed
    -- Contraction: safe when c is idempotent

  -- 19. STRONG INDUCTION
  -- DYNAMICS: Using k previous cases multiplies credences
  -- STATUS: Not yet formalized (see issue #155)
  module StrongInduction where
    -- If using k previous cases: credence degrades by factor s^k
    --
    -- Formalization would require:
    --   1. Induction schema with k-deep recursion
    --   2. Proof that credence is c * s^k after k steps
    --   3. Comparison with classical induction (k=1 case)
    --
    -- Key insight: classical strong induction uses arbitrary k
    -- without credence penalty (assumes s=1). CredTT tracks this.
    -- See: InductionDynamics in Neighbourhood.agda for k=1 case
    strong-induction-not-yet-formalized : Set
    strong-induction-not-yet-formalized = ⊤

  -- 20. CONTRAPOSITIVE
  -- DYNAMICS: Robust implication between regions
  module Contrapositive where
    -- Prove A -> B by proving not B -> not A
    -- But stability transforms! not reverses order

-- ============================================================
-- CREDTT-NATIVE PROOF TECHNIQUES (21-28)
-- No classical analogue - pure CredTT innovations
-- STATUS (Issue #119): These modules wrap record definitions from
-- StabilityTheorems.NativeTechniques. They provide type aliases and
-- examples but not full proof infrastructure. See StabilityTheorems.agda.
-- ============================================================

module CredTTNativeTechniques {ℓ} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open import CredTT.Neighbourhood
  open import CredTT.StabilityTheorems
  open StabilityDefs DM
  open NativeTechniques DM

  -- 21. STABILITY PROOFS
  -- Prove c is a post-fixed point of some operator
  module StabilityProofs where
    -- DYNAMICS FORMULATION:
    -- StabilityProof c s = PostFixedPoint c s AND Positive c
    --
    -- Examples:
    -- "2+2=4 is ROBUSTLY true" = PostFixedPoint 1 1
    -- "sqrt(2) is rational" = Invariant 0 s (degenerate fixed point)
    -- "Goedel sentence" = Idempotent at 1/2 (Interior stable!)

    -- Record combining post-fixed point with positivity
    StabilityProofRecord : C → C → Set ℓ
    StabilityProofRecord = StabilityProof

  -- 22. CREDENCE BOUNDS AS INVARIANTS
  -- Maintain c >= bound through computation
  module CredenceBounds where
    -- Track: c(A) >= 0.9 as loop invariant
    -- Upper bound: c(not A) <= 0.1

    LowerBoundRecord : C → Set ℓ
    LowerBoundRecord = LowerBound

    UpperBoundRecord : C → Set ℓ
    UpperBoundRecord = UpperBound

  -- 23. CONTINUITY/ROBUSTNESS LEMMAS
  -- Small input degradation -> small output degradation
  module ContinuityLemmas where
    -- Lipschitz condition for credence:
    -- |c(f(A)) - c(f(A'))| <= L * |c(A) - c(A')|

    -- Monotonicity lemma: multiplication preserves order
    mul-mono : ∀ {c₁ c₁' c₂ c₂'} →
      c₁' ≤ c₁ → c₂' ≤ c₂ →
      (c₁' · c₂') ≤ (c₁ · c₂)
    mul-mono = mul-monotone

  -- 24. DEGENERACY ANALYSIS
  -- How fast does credence approach 0?
  module DegeneracyAnalysis where
    -- Quantitative inconsistency diagnosis
    -- "Credence drops from 0.9 to 0.1 at step 7"

    IsDegradingDef : C → Set ℓ
    IsDegradingDef = IsDegrading

  -- 25. CONTRACTIVITY ARGUMENTS
  -- Prove step is non-degrading
  module Contractivity where
    -- For induction: need step @ 1 (contractive)
    -- If step @ 0.99: degradation over iterations

    NonDegradingDef : C → Set ℓ
    NonDegradingDef = NonDegrading

    identity-preserves : NonDegrading 𝟙
    identity-preserves = identity-non-degrading

  -- 26. PROOF FACTORING
  -- Separate high-credence core from low-credence fringe
  module ProofFactoring where
    -- Core: definitely true @ 1
    -- Fringe: probably true @ c < 1

    FactoringRecord : C → Set ℓ
    FactoringRecord = CredenceFactoring

  -- 27. DUAL PROOFS
  -- Lower bound for A + upper bound for not A = squeezed region
  module DualProofs where
    -- Prove: 0.4 <= c(A) <= 0.6
    -- The Goedel region: neither true nor false

    -- Goedel sentence: c = 1/2 exactly
    -- Squeezed by self-reference from both sides

    SqueezedRecord : C → Set ℓ
    SqueezedRecord = SqueezedCredence

  -- 28. LIMIT THEOREMS
  -- Asymptotic credence behavior
  module LimitTheorems where
    -- As n -> infinity, c(P(n)) -> L
    -- Uniform vs pointwise convergence

    -- Convergence rates:
    -- Exponential: 1 - 2^(-n)
    -- Polynomial: 1 - 1/n
    -- Logarithmic: 1 - 1/log(n)

-- ============================================================
-- TECHNIQUE SUMMARY: Classical vs Dynamics View
-- ============================================================

module TechniqueSummary where
  {-
  | Technique | Classical View | Dynamics View |
  |-----------|----------------|---------------|
  | 1. Direct | A -> A | T_1(c) = c |
  | 2. Cases | Both branches | Parallel post-fixed |
  | 3. Contrapos | (A->B) <-> (notB->notA) | not reverses order |
  | 4. Reductio | Derive contradiction | Unstable(not c) => Stable(c) |
  | 5. Ex Falso | bottom -> A | T_s(0) = 0 |
  | 6. Vacuous | False antecedent | 0 * s = 0 |
  | 7. Deduction | Lambda intro | Preserves post-fixed |
  | 8. MP | f a | T_s1 composed T_s2 = T_{s1*s2} |
  | 9. Syllogism | g composed f | Transitive composition |
  | 10. Universal | forall x. P(x) | inf_x post-fixed |
  | 11. Exists | (a, b) | c_a * c_b |
  | 12. Induction | Base + step | Post-fixed under step |
  | 13. Exhaust | All cases | All post-fixed |
  | 14. Construct | Witness | c_w * c_p |
  | 15. Refute | Derive bottom | Degenerate to 0 |
  | 16. Rewrite | a = b | Preserves post-fixed |
  | 17. Analogy | Similar | Low-credence morphism |
  | 18. Structural | Exchange/weak/contract | Conditional on credence |
  | 19. Strong Ind | Multiple previous | s^k degradation |
  | 20. Contrapos | notB -> notA | Reverses post-fixed |
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
