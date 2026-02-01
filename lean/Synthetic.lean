/-
# Synthetic Probability - Axiom Reduction Experiments

This file explores which axioms in Foundations.lean are derivable from others.
Goal: reduce axiom count for Paper 5.
-/

import Foundations

-- ============================================================================
-- EXPERIMENT 1: Deriving De Morgan from Prob axioms
-- ============================================================================

/-
Goal: Prove these as theorems, not axioms:
  - Prob.de_morgan_and : 𝟙 -ₚ (a *ₚ b) = ((𝟙 -ₚ a) +ₚ (𝟙 -ₚ b)) -ₚ ((𝟙 -ₚ a) *ₚ (𝟙 -ₚ b))
  - Prob.de_morgan_or : 𝟙 -ₚ ((a +ₚ b) -ₚ (a *ₚ b)) = (𝟙 -ₚ a) *ₚ (𝟙 -ₚ b)

Algebraic verification (for real [0,1]):
  LHS = 1 - ab
  RHS = (1-a) + (1-b) - (1-a)(1-b)
      = 1 - a + 1 - b - (1 - a - b + ab)
      = 1 - a + 1 - b - 1 + a + b - ab
      = 1 - ab = LHS ✓

For the formalization, we need intermediate lemmas about subtraction.
-/

-- Helper: what we need but may not have
-- This expresses that subtraction "undoes" addition when valid

-- Attempt 1: Try to prove de_morgan_and directly
-- theorem de_morgan_and_derived (a b : Prob) :
--     𝟙 -ₚ (a *ₚ b) = ((𝟙 -ₚ a) +ₚ (𝟙 -ₚ b)) -ₚ ((𝟙 -ₚ a) *ₚ (𝟙 -ₚ b)) := by
--   sorry -- Need more subtraction axioms

-- ============================================================================
-- REQUIRED ADDITIONAL AXIOMS (for De Morgan derivation)
-- ============================================================================

-- These would be derivable if Prob were constructed as [0,1] ⊂ ℝ
-- For now, we add them as axioms to enable the derivation

-- Subtraction is "anti-additive": (a + b) - c = a + (b - c) when b ≥ c
-- This is the associativity of subtraction in a specific direction
axiom Prob.add_sub_assoc : ∀ a b c : Prob,
  (b +ₚ c) -ₚ c = b  -- Already have this as add_sub_cancel

-- More general: subtraction distributes appropriately
-- 1 - (1 - a - b + c) = a + b - c (when all quantities are in [0,1])
-- This requires knowing the sum doesn't exceed 1

-- Alternative approach: prove for the specific case we need
-- For De Morgan: need 1 - (1 - a' - b' + a'b') where a' = 1-a, b' = 1-b
-- Since a, b ∈ [0,1], we have a', b' ∈ [0,1]
-- And a' + b' - a'b' ∈ [0,1] (this is prob_or!)

-- Key insight: a' + b' - a'b' is exactly the OR formula
-- So 1 - (1 - (a' + b' - a'b')) = a' + b' - a'b' by sub_sub_cancel

-- Let's try this approach:

-- First, show that 1 - ab = 1 - (1 - (1-a) - (1-b) + (1-a)(1-b))
-- Then use sub_sub_cancel

-- Actually, this is circular. Let me think differently.

-- ============================================================================
-- EXPERIMENT 2: Commutativity derivations
-- ============================================================================

-- These should be derivable:

theorem mul_one_from_one_mul (p : Prob) : p *ₚ 𝟙 = p := by
  rw [Prob.mul_comm]
  exact Prob.one_mul p

theorem add_zero_from_zero_add (p : Prob) : p +ₚ 𝟘 = p := by
  rw [Prob.add_comm]
  exact Prob.zero_add p

theorem mul_zero_from_zero_mul (p : Prob) : p *ₚ 𝟘 = 𝟘 := by
  rw [Prob.mul_comm]
  exact Prob.zero_mul p

-- add_mul from mul_add:
theorem add_mul_from_mul_add (p q r : Prob) : (p +ₚ q) *ₚ r = (p *ₚ r) +ₚ (q *ₚ r) := by
  rw [Prob.mul_comm, Prob.mul_comm p r, Prob.mul_comm q r]
  exact Prob.mul_add r p q

-- one_sub_one from sub_self:
theorem one_sub_one_from_sub_self : 𝟙 -ₚ 𝟙 = 𝟘 := Prob.sub_self 𝟙

-- ============================================================================
-- EXPERIMENT 3: CondExp mono from positivity
-- ============================================================================

-- If we had positivity: (∀ x, 𝟘 ≤ₚ f x) → 𝟘 ≤ₚ 𝔼[f | g]
-- Then mono follows from additivity

-- Assume positivity axiom
axiom CondExp.positivity {α : Type} (f g : ProbProp α) :
  (∀ x, 𝟘 ≤ₚ f x) → 𝟘 ≤ₚ 𝔼[f | g]

-- Need subtraction for ProbProp
noncomputable def prob_sub {α : Type} (f g : ProbProp α) : ProbProp α :=
  fun x => f x -ₚ g x

-- Derive mono from positivity + additivity
-- If f ≤ f' pointwise, then f' - f ≥ 0 pointwise
-- E[f' | g] = E[f | g] + E[f' - f | g]
-- By positivity, E[f' - f | g] ≥ 0
-- So E[f' | g] ≥ E[f | g]

-- This requires: E[f' | g] = E[f | g] + E[f' - f | g]
-- Which needs: f' = f + (f' - f), i.e., f + (f' - f) = f' pointwise
-- This is: p + (q - p) = q when q ≥ p

-- We need an axiom for this
axiom Prob.add_sub_of_le : ∀ p q : Prob, p ≤ₚ q → p +ₚ (q -ₚ p) = q

theorem CondExp_mono_from_positivity {α : Type} (f f' g : ProbProp α) :
    (∀ x, f x ≤ₚ f' x) → 𝔼[f | g] ≤ₚ 𝔼[f' | g] := by
  intro hle
  -- f' = f + (f' - f) pointwise
  have heq : ∀ x, f' x = f x +ₚ (f' x -ₚ f x) := fun x => (Prob.add_sub_of_le (f x) (f' x) (hle x)).symm
  -- So E[f' | g] = E[f + (f' - f) | g] = E[f | g] + E[f' - f | g]
  have hadd : 𝔼[f' | g] = 𝔼[f | g] +ₚ 𝔼[prob_sub f' f | g] := by
    have h1 : 𝔼[f' | g] = 𝔼[(fun x => f x +ₚ (f' x -ₚ f x)) | g] := by
      congr 1
      funext x
      exact heq x
    rw [h1]
    exact CondExp.add f (prob_sub f' f) g
  -- By positivity, E[f' - f | g] ≥ 0
  have hpos : 𝟘 ≤ₚ 𝔼[prob_sub f' f | g] := by
    apply CondExp.positivity
    intro x
    unfold prob_sub
    -- f x ≤ f' x, so f' x - f x ≥ 0
    -- Need: q - p ≥ 0 when q ≥ p
    sorry -- Need axiom: sub_nonneg_of_le
  -- So E[f | g] ≤ E[f | g] + E[f' - f | g] = E[f' | g]
  rw [hadd]
  -- Need: p ≤ p + q when 0 ≤ q
  sorry -- Need axiom: le_add_of_nonneg

-- ============================================================================
-- SUMMARY OF NEEDED AXIOMS FOR DERIVATIONS
-- ============================================================================

/-
To derive De Morgan:
  - Need either direct algebraic manipulation axioms for subtraction
  - Or: prove via the semantic interpretation (Prob = [0,1])

To derive mono from positivity:
  - Prob.add_sub_of_le : p ≤ q → p + (q - p) = q
  - Prob.sub_nonneg_of_le : p ≤ q → 0 ≤ q - p
  - Prob.le_add_of_nonneg : 0 ≤ q → p ≤ p + q

These are all true for [0,1] ⊂ ℝ but not currently axiomatized.

Conclusion: Axiom reduction is possible but requires:
  1. More subtraction axioms, OR
  2. Constructing Prob as [0,1] and deriving all axioms
-/

-- ============================================================================
-- EXPERIMENT 4: Finite Prob operations
-- ============================================================================

-- For finite types, we can define max/min over Prob values
-- This would enable proving finite prob_zorn

-- Requires: Fintype α, DecidableEq on Prob
-- Currently blocked: Prob is abstract with no decidable equality

-- ============================================================================
-- NEXT STEPS
-- ============================================================================

/-
1. Option A: Add the missing subtraction axioms
   - Makes derivations work
   - Increases axiom count temporarily
   - Clean up later when Prob is constructed

2. Option B: Construct Prob as [0,1] using Mathlib
   - All axioms become theorems
   - Requires Mathlib dependency
   - Changes the synthetic nature

3. Option C: Keep current axioms, focus on prob_zorn
   - Accept current axiom count
   - Prove prob_zorn for finite types first
   - Extend to infinite via projective limits

Recommended: Option C for Paper 5 v1, then Option B for v2.
-/
