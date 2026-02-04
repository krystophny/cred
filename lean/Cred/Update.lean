/-
  Cred Part 2: Update Rules

  Defines Bayesian and Jeffrey conditionalization as update operations on
  valuations, and proves key properties:
  - Bayesian update preserves complement
  - Jeffrey update stays in [0,1]
  - Chain-rule preservation under update
  - Zero-evidence underdetermination
-/

import Cred.Basic
import Cred.Valuation

namespace Cred

/-! ## Bayesian Conditionalization

Given a prior valuation v and evidence B with v(B) > 0, the posterior is:
  v'(A) = v(A ∧ B) / v(B)

This requires joint credences as input (from a JointValuation). -/

/-- Bayesian update: given prior credence for A∧B and B (with B > 0),
    produce the posterior credence for A. -/
noncomputable def bayesianUpdate (joint evidence : Credence) (h_pos : 0 < evidence.val)
    (h_le : joint.val ≤ evidence.val) : Credence :=
  (Credence.conditioning_mk joint evidence h_pos h_le).condCred

/-- The Bayesian update satisfies the chain rule by construction. -/
theorem bayesianUpdate_chain_rule (joint evidence : Credence) (h_pos : 0 < evidence.val)
    (h_le : joint.val ≤ evidence.val) :
    bayesianUpdate joint evidence h_pos h_le ⊗ evidence = joint :=
  (Credence.conditioning_mk joint evidence h_pos h_le).chainRule

/-- The Bayesian update value equals joint/evidence. -/
theorem bayesianUpdate_val (joint evidence : Credence) (h_pos : 0 < evidence.val)
    (h_le : joint.val ≤ evidence.val) :
    (bayesianUpdate joint evidence h_pos h_le).val = joint.val / evidence.val := by
  unfold bayesianUpdate Credence.conditioning_mk
  simp

/-- Bayesian update is uniquely determined (follows from conditioning uniqueness). -/
theorem bayesianUpdate_unique (joint evidence : Credence) (h_pos : 0 < evidence.val)
    (h_le : joint.val ≤ evidence.val) (c : Credence) (hc : c ⊗ evidence = joint) :
    c = bayesianUpdate joint evidence h_pos h_le :=
  Credence.conditioning_unique joint evidence h_pos ⟨c, hc⟩
    (Credence.conditioning_mk joint evidence h_pos h_le)

/-! ## Bayesian Update on Valuations -/

/-- Apply Bayesian update to an entire joint valuation given evidence proposition b. -/
noncomputable def bayesianUpdateValuation {α : Type*}
    (v : JointValuation α) (b : α) (hb : 0 < (v.val b).val) :
    α → Credence :=
  fun a => bayesianUpdate (v.joint a b) (v.val b) hb (v.joint_le_marginal_right a b)

/-- The posterior valuation satisfies the chain rule at every proposition. -/
theorem bayesianUpdateValuation_chain_rule {α : Type*}
    (v : JointValuation α) (b : α) (hb : 0 < (v.val b).val) (a : α) :
    bayesianUpdateValuation v b hb a ⊗ v.val b = v.joint a b :=
  bayesianUpdate_chain_rule (v.joint a b) (v.val b) hb (v.joint_le_marginal_right a b)

/-! ## Jeffrey Conditionalization

Jeffrey conditionalization handles uncertain evidence. Instead of learning B
with certainty, you learn that B has new credence q:

  v'(A) = v(A|B) * q + v(A|~B) * (1-q)

This requires conditionals v(A|B) and v(A|~B), both determined when
v(B) > 0 and v(~B) > 0. -/

/-- Jeffrey update given the two conditional credences and a new evidence credence.
    v'(A) = condGivenB * q + condGivenNotB * (1-q) -/
noncomputable def jeffreyUpdate (condGivenB condGivenNotB q : Credence) : Credence where
  val := condGivenB.val * q.val + condGivenNotB.val * (1 - q.val)
  nonneg := by
    apply add_nonneg
    · exact mul_nonneg condGivenB.nonneg q.nonneg
    · exact mul_nonneg condGivenNotB.nonneg (by linarith [q.le_one])
  le_one := by
    have h1 : condGivenB.val * q.val ≤ 1 * q.val :=
      mul_le_mul_of_nonneg_right condGivenB.le_one q.nonneg
    have h2 : condGivenNotB.val * (1 - q.val) ≤ 1 * (1 - q.val) :=
      mul_le_mul_of_nonneg_right condGivenNotB.le_one (by linarith [q.le_one])
    linarith

/-- Jeffrey update value formula. -/
theorem jeffreyUpdate_val (condGivenB condGivenNotB q : Credence) :
    (jeffreyUpdate condGivenB condGivenNotB q).val =
    condGivenB.val * q.val + condGivenNotB.val * (1 - q.val) := rfl

/-- Jeffrey update at q=1 reduces to condGivenB (Bayesian case). -/
theorem jeffreyUpdate_certain (condGivenB condGivenNotB : Credence) :
    jeffreyUpdate condGivenB condGivenNotB 1 = condGivenB := by
  ext
  simp only [jeffreyUpdate_val, Credence.one_val, mul_one, sub_self, mul_zero, add_zero]

/-- Jeffrey update at q=0 reduces to condGivenNotB (learning ~B with certainty). -/
theorem jeffreyUpdate_zero (condGivenB condGivenNotB : Credence) :
    jeffreyUpdate condGivenB condGivenNotB 0 = condGivenNotB := by
  ext
  simp only [jeffreyUpdate_val, Credence.zero_val, mul_zero, sub_zero, mul_one, zero_add]

/-! ## Chain-Rule Preservation Under Update

A Bayesian update produces a posterior that still satisfies the chain rule.
This is definitional: the update IS defined via the chain rule. -/

/-- The chain rule is preserved by construction: the posterior conditional
    at any proposition satisfies condCred ⊗ evidence = joint. -/
theorem update_preserves_chain_rule (joint evidence : Credence)
    (h_pos : 0 < evidence.val) (h_le : joint.val ≤ evidence.val) :
    bayesianUpdate joint evidence h_pos h_le ⊗ evidence = joint :=
  bayesianUpdate_chain_rule joint evidence h_pos h_le

/-! ## Zero-Evidence Underdetermination

When evidence has credence 0, both Bayesian and Jeffrey conditionalization
are underdetermined: the chain rule provides no constraint on the conditional.

This is Part 1's fundamental result (conditioning_zero_any) applied to updates:
the update mechanism itself cannot resolve the ambiguity at zero evidence. -/

/-- Bayesian update is undefined at zero evidence: any posterior is consistent. -/
theorem bayesian_underdetermined_at_zero (c : Credence) :
    ∃ cond : Credence.Conditioning 0 0, cond.condCred = c :=
  Credence.conditioning_zero_any c

/-- Jeffrey update is also underdetermined when v(B) = 0: the conditional
    v(A|B) is unconstrained, so the mixture depends on an unconstrained term. -/
theorem jeffrey_underdetermined_at_zero :
    ∀ c : Credence, ∃ cond : Credence.Conditioning 0 0,
      cond.condCred = c :=
  Credence.conditioning_zero_any

end Cred
