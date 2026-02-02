-- Proof Techniques in CredTT
--
-- STATUS: PEDAGOGICAL TEMPLATES WITH DYNAMICS FRAMEWORK
--
-- This module provides MODULE STRUCTURE and DOCUMENTATION for all 28 proof
-- techniques. It connects to the dynamics framework where:
--
-- KEY INSIGHT: Proofs are MONOTONE OPERATORS on credences
-- - Each proof step s induces operator T_s(c) = c · s
-- - Stability is about FIXED POINTS of these operators
-- - PostFixedPoint: c ≤ c · s (step doesn't reduce credence)
-- - Invariant: c = c · s (exact fixed point)
-- - Idempotent: c · c = c (self-stable, may be interior!)
--
-- For the actual proven stability theorems, see:
-- - CredTT.StabilityTheorems (proven dynamics lemmas)
-- - CredTT.Neighbourhood (order-theoretic definitions)
-- - CredTT.Collapse (proven {0,1} collapse theorem)
--
-- Each technique shows WHY CredTT is more expressive than MLTT:
-- Classical logic hides credence dynamics; CredTT exposes them.

module CredTT.ProofTechniques where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool using (Bool; true; false; not)
open import Function using (_∘_; id)

open import CredTT.Credence

-- ============================================================
-- CLASSICAL PROOF TECHNIQUES (1-20)
-- ============================================================

module ClassicalTechniques {ℓ} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open import CredTT.Neighbourhood
  open import CredTT.StabilityTheorems
  open StabilityDefs DM        -- includes DynamicsDefs (PostFixedPoint, Invariant, etc.)
  open ClassicalRecovery DM    -- proven dynamics versions
  open OperatorDynamics DM     -- T_s(c) = c · s operator

  -- 1. DIRECT PROOF
  -- Track credence accumulation via multiplication
  module DirectProof where
    -- Example: identity function at credence 1
    direct-example : ∀ {A : Set} → A → A
    direct-example a = a

    -- Credence: input @ c → output @ c (preserved)
    -- In MLTT: just "A → A"
    -- In CredTT: "A @ c → A @ c" with c tracked

  -- 2. PROOF BY CASES
  -- Each branch stable → result stable
  module ProofByCases where
    -- Example: case analysis on Bool
    cases-example : ∀ (b : Bool) → (b ≡ true) ⊎ (b ≡ false)
    cases-example true = inj₁ refl
    cases-example false = inj₂ refl

    -- Stability: if both branches are Stable₁, result is Stable₁
    -- If either branch is Unstable₀, result might be Unstable₀

  -- 3. CONTRAPOSITION
  -- Stability-based, not exact equivalence
  module Contraposition where
    -- Classical: (A → B) ↔ (¬B → ¬A)
    -- CredTT: stability transforms under negation

    -- Note: True contraposition requires negation types
    -- This is just a placeholder showing module structure
    contrapos-id : ∀ {A : Set} → (A → A) → (A → A)
    contrapos-id f = f

    -- The KEY: negation flips stability
    -- Stable₁(A→B) doesn't mean Stable₁(¬B→¬A)
    -- The STABILITY transforms, not just the truth

  -- 4. REDUCTIO AD ABSURDUM
  -- Unstable negation implies stable positive
  module Reductio where
    -- Example: sqrt(2) irrationality
    -- Assume rational @ c, derive contradiction, c → 0
    -- Therefore irrational @ 1

    -- In CredTT: Unstable₀(¬A) ⇒ Stable₁(A)
    -- This is the stability reflection principle

  -- 5. EX FALSO QUODLIBET
  -- At credence 0, any conditional is admissible
  module ExFalso where
    -- Classical: ⊥ → A
    -- CredTT: at c = 0, constraints vanish

    -- Graded spectrum:
    -- c = 1: fully constrained
    -- c = 0.5: weakly constrained
    -- c = 0: unconstrained (ex falso)

  -- 6. VACUOUS TRUTH
  -- Near-zero antecedent → weakly constrained conditional
  module VacuousTruth where
    -- Classical: "If pigs fly, then 2+2=5" is TRUE
    -- CredTT: conditional at c ≈ 0 is UNCONSTRAINED, not TRUE

  -- 7. DEDUCTION THEOREM
  -- Lambda abstraction preserves credence and stability
  module DeductionTheorem where
    -- Classical: Γ, A ⊢ B implies Γ ⊢ A → B
    -- CredTT: Γ, x:A ⊢ b:B @ c implies Γ ⊢ λx.b : A→B @ c

    deduction-example : ∀ {A B : Set} → (A → B) → (A → B)
    deduction-example f = f

    -- Stability preserved: stable body → stable lambda

  -- 8. MODUS PONENS
  -- Credences MULTIPLY in application
  module ModusPonens where
    -- f : A → B @ c₁, a : A @ c₂ ⊢ f a : B @ c₁ · c₂

    mp-example : ∀ {A B : Set} → (A → B) → A → B
    mp-example f a = f a

    -- This is the CHAIN RULE: P(B) = P(B|A) · P(A)
    -- Stability: Stable₁ · Stable₁ = Stable₁

  -- 9. SYLLOGISM
  -- Function composition, credences multiply
  module Syllogism where
    -- f : A → B @ c₁, g : B → C @ c₂ ⊢ g ∘ f : A → C @ c₁ · c₂

    syl-example : ∀ {A B C : Set} → (A → B) → (B → C) → (A → C)
    syl-example f g = g ∘ f

    -- Long chains degrade: c₁ · c₂ · ... · cₙ
    -- Stability: compose stable = stable

  -- 10. UNIVERSAL GENERALIZATION
  -- Credence is infimum over instances
  module UniversalGen where
    -- Classical: ∀x. P(x) from arbitrary P(x)
    -- CredTT: ∀x. P(x) @ inf{c(x)}

    univ-example : ∀ (n : ℕ) → n + 0 ≡ n
    univ-example zero = refl
    univ-example (suc n) = cong suc (univ-example n)

    -- If every instance @ 1, universal @ 1
    -- If one instance @ 0.5, universal might be @ 0.5

  -- 11. EXISTENTIAL INTRODUCTION/ELIMINATION
  -- Credences multiply: witness · property
  module Existential where
    -- (a, b) : Σx:A. B(x) @ c_a · c_b

    exist-example : Σ ℕ (λ n → n + n ≡ 4)
    exist-example = 2 , refl

    -- Witness @ c₁, property @ c₂ → existence @ c₁ · c₂

  -- 12. NATURAL INDUCTION
  -- Valid iff c is a post-fixed point of step operator
  module NaturalInduction where
    -- DYNAMICS FORMULATION:
    -- Induction valid iff c ≤ c · step (PostFixedPoint c step)
    --
    -- Classical: step = 1, so c ≤ c · 1 = c always holds
    -- Interior: if c idempotent (c · c = c), induction at c is valid!
    --
    -- See: InductionDynamics.InductionValid for the formal definition

    ind-example : ∀ (n : ℕ) → n + 0 ≡ n
    ind-example zero = refl
    ind-example (suc n) = cong suc (ind-example n)

    -- If step @ 1: PostFixedPoint holds trivially (T_1 = identity)
    -- If step < 1 and non-idempotent: may degrade over iterations

  -- 13. PROOF BY EXHAUSTION
  -- Stable if all cases stable
  module Exhaustion where
    -- Check all cases: result @ product of credences

    exhaust-example : ∀ (b : Bool) → not (not b) ≡ b
    exhaust-example true = refl
    exhaust-example false = refl

    -- 2 cases @ 1 → result @ 1 · 1 = 1

  -- 14. CONSTRUCTIVE PROOF
  -- Witness with credence certificate
  module Construction where
    -- Exhibit witness @ c, verify property @ d → existence @ c · d

    construct-example : ∃ (λ n → n * n ≡ 4)
    construct-example = 2 , refl

  -- 15. REFUTATION
  -- Drive credence to 0
  module Refutation where
    -- Classical: derive ⊥
    -- CredTT: drive c → 0 (degeneracy)

    -- Quantitative: how fast does c approach 0?

  -- 16. EQUATIONAL REWRITING
  -- If equality stable, rewriting preserves stability
  module Equational where
    -- Rewrite with eq : a ≡ b @ c
    -- Result credence multiplies by c

    rewrite-example : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    rewrite-example = trans

  -- 17. PROOF BY ANALOGY
  -- Low-credence morphism (CredTT can express this!)
  module Analogy where
    -- "A is like B" @ 0.7 (explicitly weak)
    -- Transfer knowledge with visible weakness

  -- 18. STRUCTURAL RULES
  -- Exchange free, weakening/contraction conditional
  module StructuralRulesExample where
    -- Exchange: always free
    -- Weakening: only if added @ 1
    -- Contraction: requires permission

    exchange-example : ∀ {A B C : Set} → (A → B → C) → (B → A → C)
    exchange-example f b a = f a b

  -- 19. STRONG INDUCTION
  -- Using multiple previous cases multiplies credences
  module StrongInduction where
    -- If using k previous cases: credence degrades faster

  -- 20. CONTRAPOSITIVE
  -- Robust implication between regions
  module Contrapositive where
    -- Prove A → B by proving ¬B → ¬A
    -- But stability transforms!


-- ============================================================
-- CREDTT-NATIVE PROOF TECHNIQUES (21-28)
-- No classical analogue - pure CredTT innovations
-- ============================================================

module CredTTNativeTechniques {ℓ} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open import CredTT.Neighbourhood
  open import CredTT.StabilityTheorems
  open StabilityDefs DM        -- includes DynamicsDefs
  open NativeTechniques DM     -- StabilityProof, InvariantProof records

  -- 21. STABILITY PROOFS
  -- Prove c is a post-fixed point of some operator
  module StabilityProofs where
    -- DYNAMICS FORMULATION:
    -- StabilityProof c s = PostFixedPoint c s × Positive c
    -- (prove: the operator T_s doesn't reduce credence below c)
    --
    -- See: NativeTechniques.StabilityProof record
    --
    -- Examples:
    -- "2+2=4 is ROBUSTLY true" = PostFixedPoint 1 1
    -- "sqrt(2) is rational" = Invariant 0 s (degenerate fixed point)
    -- "Gödel sentence" = Idempotent at 1/2 (Interior stable!)

  -- 22. CREDENCE BOUNDS AS INVARIANTS
  -- Maintain c ≥ bound through computation
  module CredenceBounds where
    -- Track: c(A) ≥ 0.9 as loop invariant
    -- Upper bound: c(¬A) ≤ 0.1

    -- Dual bounds: l ≤ c(A) ≤ u
    -- Squeeze credence into interval

  -- 23. CONTINUITY/ROBUSTNESS LEMMAS
  -- Small input degradation → small output degradation
  module ContinuityLemmas where
    -- Lipschitz condition for credence:
    -- |c(f(A)) - c(f(A'))| ≤ L · |c(A) - c(A')|

    -- If L = 1: input error = output error
    -- If L < 1: errors decrease (contractive)
    -- If L > 1: errors amplify

  -- 24. DEGENERACY ANALYSIS
  -- How fast does credence approach 0?
  module DegeneracyAnalysis where
    -- Quantitative inconsistency diagnosis
    -- "Credence drops from 0.9 to 0.1 at step 7"
    -- Pinpoint problematic steps

  -- 25. CONTRACTIVITY ARGUMENTS
  -- Prove step is non-degrading
  module Contractivity where
    -- For induction: need step @ 1 (contractive)
    -- If step @ 0.99: degradation over iterations

    -- Prove: step preserves credence (non-degrading)
    -- Or: bound the degradation rate

  -- 26. PROOF FACTORING
  -- Separate high-credence core from low-credence fringe
  module ProofFactoring where
    -- Core: definitely true @ 1
    -- Fringe: probably true @ c < 1

    -- If fringe invalidated, core still stands
    -- Modular credence analysis

  -- 27. DUAL PROOFS
  -- Lower bound for A + upper bound for ¬A = squeezed region
  module DualProofs where
    -- Prove: 0.4 ≤ c(A) ≤ 0.6
    -- The Gödel region: neither true nor false

    -- Gödel sentence: c = 1/2 exactly
    -- Squeezed by self-reference from both sides

  -- 28. LIMIT THEOREMS
  -- Asymptotic credence behavior
  module LimitTheorems where
    -- As n → ∞, c(P(n)) → L
    -- Uniform vs pointwise convergence

    -- Convergence rates:
    -- Exponential: 1 - 2^(-n)
    -- Polynomial: 1 - 1/n
    -- Logarithmic: 1 - 1/log(n)


-- ============================================================
-- CONCRETE EXAMPLES: Classical vs CredTT
-- ============================================================

module ConcreteExamples where
  open ClassicalTechniques

  -- Example 1: Modus Ponens with Credence
  -- Classical: A, A → B ⊢ B
  -- CredTT: A @ 0.9, (A → B) @ 0.95 ⊢ B @ 0.855

  -- Example 2: Long Syllogism
  -- 10 steps, each @ 0.99
  -- Classical: definitely true
  -- CredTT: 0.99^10 = 0.904 (not as confident!)

  -- Example 3: Induction over ℕ
  -- Classical: base + step ⊢ ∀n.P(n)
  -- CredTT: step @ 0.999, P(1000) @ 0.999^1000 ≈ 0.37

  -- Example 4: Gödel Sentence
  -- Classical: undecidable
  -- CredTT: c = 1/2 exactly (Interior, not Stable or Unstable)

  -- Example 5: Stability Proof
  -- "2+2=4 is robust" = Stable₁
  -- This is a META-THEOREM that classical logic cannot express!
