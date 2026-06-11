/-
  Cred Fixpoint Library

  A self-referential definition is treated as an equation c = Φ c. Its
  meanings are the solution set of that equation. This module records the
  concrete solution sets used by the foundations paper.
-/

import Cred.Bridge.Curry
import Mathlib.Dynamics.FixedPoints.Basic

namespace Cred

namespace Credence

/-- Solution set of a self-map on credences. -/
def solutions (Φ : Credence → Credence) : Set Credence := {c | Φ c = c}

theorem mem_solutions_iff (Φ : Credence → Credence) (c : Credence) :
    c ∈ solutions Φ ↔ Φ c = c := Iff.rfl

theorem solutions_eq_fixedPoints (Φ : Credence → Credence) :
    solutions Φ = Function.fixedPoints Φ := rfl

/-! ## Negation and Truth-Teller -/

theorem solutions_neg_eq_singleton :
    solutions neg = {half} := by
  ext c
  constructor
  · intro h
    simpa [Set.mem_singleton_iff] using neg_fixed_point_unique c h
  · intro h
    rw [Set.mem_singleton_iff] at h
    rw [h]
    exact liar_fixed_point

theorem liar_solution :
    half ∈ solutions neg := by
  exact liar_fixed_point

theorem solutions_id_eq_univ :
    solutions (fun c : Credence => c) = Set.univ := by
  ext c
  simp [solutions]

theorem truth_teller_any (c : Credence) :
    c ∈ solutions (fun x : Credence => x) := by
  simp [solutions]

theorem truth_teller_same_shape_as_zero_evidence :
    solutions (fun c : Credence => c) = Cond 0 0 := by
  rw [solutions_id_eq_univ, cond_zero_zero_univ]

/-! ## Crisp Contrast -/

def boolNegSolutions : Set Bool := {b | !b = b}

theorem bool_neg_solutions_empty :
    boolNegSolutions = ∅ := by
  ext b
  cases b <;> simp [boolNegSolutions]

/-! ## Curry Residuum -/

noncomputable def sqrtCred (b : Credence) : Credence where
  val := Real.sqrt b.val
  nonneg := Real.sqrt_nonneg b.val
  le_one := by
    calc Real.sqrt b.val ≤ Real.sqrt 1 := Real.sqrt_le_sqrt b.le_one
      _ = 1 := Real.sqrt_one

@[simp] theorem sqrtCred_val (b : Credence) :
    (sqrtCred b).val = Real.sqrt b.val := rfl

theorem curry_sqrt_solution (b : Credence) (hb : 0 < b.val) :
    sqrtCred b ∈ solutions (fun x : Credence => prodResid x b) := by
  change prodResid (sqrtCred b) b = sqrtCred b
  ext
  have hcpos : 0 < (sqrtCred b).val := by
    simp [sqrtCred, Real.sqrt_pos.2 hb]
  rw [prodResid_pos_val (sqrtCred b) b hcpos]
  have hsqrtnz : Real.sqrt b.val ≠ 0 := ne_of_gt (by simpa [sqrtCred] using hcpos)
  have hdiv : b.val / Real.sqrt b.val = Real.sqrt b.val := by
    rw [div_eq_iff hsqrtnz]
    nth_rewrite 1 [← Real.sq_sqrt b.nonneg]
    ring
  have hsqrt_le_one : Real.sqrt b.val ≤ 1 := (sqrtCred b).le_one
  simp [sqrtCred, hdiv, min_eq_left hsqrt_le_one]

theorem curry_solutions_nonempty_positive (b : Credence) (hb : 0 < b.val) :
    (solutions (fun x : Credence => prodResid x b)).Nonempty := by
  exact ⟨sqrtCred b, curry_sqrt_solution b hb⟩

theorem curry_zero_solutions_empty :
    solutions (fun c : Credence => prodResid c 0) = ∅ := by
  ext c
  constructor
  · intro h
    exact False.elim (curry_no_fixed_point_zero ⟨c, h.symm⟩)
  · intro h
    exact False.elim (Set.not_mem_empty c h)

/-! ## Russell Link -/

theorem russell_scalar_solutions :
    solutions neg = {half} := solutions_neg_eq_singleton

end Credence

end Cred
