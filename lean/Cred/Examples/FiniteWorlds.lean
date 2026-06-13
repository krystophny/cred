/-
  Cred Examples: the four-world toy model (issue #638)

  A finite world space `W := Fin 4` with three Boolean propositions

      A = [1,1,0,0],  B = [1,0,1,0],  C = [1,1,1,1]   over w0..w3.

  Two layers live side by side over the same worlds:

  - Semantic entailment `Entails A B := ∀ w, A w → B w`, which coincides with
    truth-set inclusion (`entails_iff_subset`). `A` does not entail `B`
    (countermodel `w1`), but `A` entails the tautology `C`. Pointwise agreement
    at a single world (`w0`) does NOT determine the global entailment relation.

  - A probabilistic layer: a weight `μ : W → ℚ` summing to 1 and
    `P A := ∑ w, if A w then μ w else 0`. Two weightings with the SAME marginals
    `P A`, `P B` differ on the joint `P (A∧B)` (`joint_not_determined_by_marginals`):
    marginals do not fix the joint.

  No measure theory; the probability is an explicit `Finset.sum` of rationals.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Cred.Core.Value

namespace Cred.Examples.FiniteWorlds

open Cred Credence

/-! ## Worlds and propositions -/

/-- The four-world space. -/
abbrev W := Fin 4

/-- A Boolean proposition over worlds. -/
abbrev BoolProp := W → Bool

/-- Crisp embedding of a Boolean proposition into a credence (0 or 1). -/
def toCred (A : BoolProp) (w : W) : Credence := if A w then 1 else 0

@[simp] theorem toCred_true (A : BoolProp) (w : W) (h : A w = true) :
    toCred A w = 1 := by simp [toCred, h]

@[simp] theorem toCred_false (A : BoolProp) (w : W) (h : A w = false) :
    toCred A w = 0 := by simp [toCred, h]

/-- `A = [1,1,0,0]`. -/
def A : BoolProp := ![true, true, false, false]

/-- `B = [1,0,1,0]`. -/
def B : BoolProp := ![true, false, true, false]

/-- `C = [1,1,1,1]` (the tautology). -/
def C : BoolProp := ![true, true, true, true]

/-- Pointwise conjunction of two propositions. -/
def conjProp (A B : BoolProp) : BoolProp := fun w => A w && B w

/-! ## Truth sets and entailment -/

/-- The truth set of a proposition: the worlds where it holds. -/
def truthSet (A : BoolProp) : Finset W := Finset.univ.filter (fun w => A w = true)

@[simp] theorem mem_truthSet (A : BoolProp) (w : W) :
    w ∈ truthSet A ↔ A w = true := by simp [truthSet]

/-- Semantic entailment over worlds: every `A`-world is a `B`-world. -/
def Entails (A B : BoolProp) : Prop := ∀ w, A w = true → B w = true

/-- Entailment is truth-set inclusion. -/
theorem entails_iff_subset (A B : BoolProp) :
    Entails A B ↔ truthSet A ⊆ truthSet B := by
  constructor
  · intro h w hw
    rw [mem_truthSet] at hw ⊢
    exact h w hw
  · intro h w hw
    have : w ∈ truthSet A := (mem_truthSet A w).mpr hw
    exact (mem_truthSet B w).mp (h this)

/-- `A` does not entail `B`: world `w1` is an `A`-world but not a `B`-world. -/
theorem A_not_entails_B : ¬ Entails A B := by
  intro h
  have hb : B 1 = true := h 1 (by decide)
  exact absurd hb (by decide)

/-- `A` entails the tautology `C`. -/
theorem A_entails_C : Entails A C := by
  intro w _
  fin_cases w <;> decide

/-- Pointwise agreement at a single world does not determine global entailment:
    at `w0` all of `A`, `B` are true, yet `A` does not entail `B`. -/
theorem pointwise_does_not_determine :
    A 0 = true ∧ B 0 = true ∧ ¬ Entails A B :=
  ⟨by decide, by decide, A_not_entails_B⟩

/-! ## Probabilistic layer: marginals do not determine the joint

A weight `μ : W → ℚ` summing to 1; `P A` is the total weight of `A`-worlds.
Two weightings `μ1`, `μ2` share the marginals `P A = P B = 1/2` but differ on
the joint `P (A∧B)`. -/

/-- Probability of a proposition under a rational weighting. -/
def P (μ : W → ℚ) (A : BoolProp) : ℚ := ∑ w, if A w then μ w else 0

/-- Uniform weighting `[1/4, 1/4, 1/4, 1/4]`. -/
def μ1 : W → ℚ := ![1/4, 1/4, 1/4, 1/4]

/-- Correlated weighting `[1/2, 0, 0, 1/2]`. -/
def μ2 : W → ℚ := ![1/2, 0, 0, 1/2]

/-- Both weightings are probability vectors (sum to 1). -/
theorem μ1_sum : ∑ w, μ1 w = 1 := by
  norm_num [μ1, Fin.sum_univ_four]

theorem μ2_sum : ∑ w, μ2 w = 1 := by
  norm_num [μ2, Fin.sum_univ_four]

/-- The two weightings share the marginal of `A`. -/
theorem marginal_A_eq : P μ1 A = P μ2 A := by
  norm_num [P, A, μ1, μ2, Fin.sum_univ_four]

/-- The two weightings share the marginal of `B`. -/
theorem marginal_B_eq : P μ1 B = P μ2 B := by
  norm_num [P, B, μ1, μ2, Fin.sum_univ_four]

/-- The joint `P (A∧B)` under the uniform weighting is `1/4`. -/
theorem joint_μ1 : P μ1 (conjProp A B) = 1/4 := by
  norm_num [P, conjProp, A, B, μ1, Fin.sum_univ_four]

/-- The joint `P (A∧B)` under the correlated weighting is `1/2`. -/
theorem joint_μ2 : P μ2 (conjProp A B) = 1/2 := by
  norm_num [P, conjProp, A, B, μ2, Fin.sum_univ_four]

/-- The two weightings disagree on the joint `P (A∧B)`: the marginals do not
    determine the joint credence. -/
theorem joint_not_determined_by_marginals :
    P μ1 A = P μ2 A ∧ P μ1 B = P μ2 B ∧
      P μ1 (conjProp A B) ≠ P μ2 (conjProp A B) := by
  refine ⟨marginal_A_eq, marginal_B_eq, ?_⟩
  rw [joint_μ1, joint_μ2]; norm_num

/-! ## Issue #638 anchor names

The following names are the exact anchors the paper cites; they restate the
results above. -/

/-- Truth-set inclusion is entailment (issue anchor for `entails_iff_subset`). -/
theorem truthSet_subset_iff_entails (A B : BoolProp) :
    truthSet A ⊆ truthSet B ↔ Entails A B :=
  (entails_iff_subset A B).symm

/-- Pointwise truth at one world does not establish the entailment connection. -/
theorem finite_pointwise_truth_not_connection :
    A 0 = true ∧ B 0 = true ∧ ¬ Entails A B :=
  pointwise_does_not_determine

/-- Equal marginals, different joint: marginals do not fix the joint credence. -/
theorem finite_same_marginals_different_joint :
    P μ1 A = P μ2 A ∧ P μ1 B = P μ2 B ∧
      P μ1 (conjProp A B) ≠ P μ2 (conjProp A B) :=
  joint_not_determined_by_marginals

/-- Independence witness: under the uniform weighting `μ1` the joint
    `P (A∧B) = 1/4` equals the product of marginals `P A · P B = 1/2 · 1/2`. -/
theorem finite_independence_example :
    P μ1 (conjProp A B) = P μ1 A * P μ1 B := by
  norm_num [P, conjProp, A, B, μ1, Fin.sum_univ_four]

end Cred.Examples.FiniteWorlds
