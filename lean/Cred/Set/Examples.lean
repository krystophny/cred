/-
  Cred Set: Finite Relational Examples

  Small concrete CredSets over `Fin 3` exercising the graded-membership algebra.
  `evens` and `odds` are crisp partitions of `{0, 1, 2}` by parity; `graded` is a
  genuinely graded set taking the value `half` at index 1. The lemmas pin the
  membership values index by index and read off the complement, intersection, and
  union values, plus one pointwise subset relation.

  Tactic note: after `fin_cases i` the goal carries an unreduced motive, so an
  index-specific `rw` does not match. The proofs use `simp` (which reduces the
  motive) over the membership definitions and the pointwise operation lemmas.
-/

import Cred.Set.Classical

namespace Cred

namespace CredSet

open Credence

/-- The even indices of `Fin 3`: members `0` and `2`, non-member `1`. -/
def evens : CredSet (Fin 3) := ⟨fun i => if i = 1 then 0 else 1⟩

/-- The odd indices of `Fin 3`: member `1`, non-members `0` and `2`. -/
def odds : CredSet (Fin 3) := ⟨fun i => if i = 1 then 1 else 0⟩

/-- A graded set: certain at `0` and `2`, uncertain (`half`) at `1`. -/
noncomputable def graded : CredSet (Fin 3) := ⟨fun i => if i = 1 then half else 1⟩

@[simp] theorem evens_mem (i : Fin 3) : evens.mem i = if i = 1 then 0 else 1 := rfl
@[simp] theorem odds_mem (i : Fin 3) : odds.mem i = if i = 1 then 1 else 0 := rfl
@[simp] theorem graded_mem (i : Fin 3) :
    graded.mem i = if i = 1 then half else 1 := rfl

/-! ## Concrete Membership Values -/

example : evens.mem 0 = 1 := by simp
example : evens.mem 1 = 0 := by simp
example : evens.mem 2 = 1 := by simp

example : odds.mem 0 = 0 := by simp
example : odds.mem 1 = 1 := by simp
example : odds.mem 2 = 0 := by simp

example : graded.mem 0 = 1 := by simp
example : graded.mem 1 = half := by simp
example : graded.mem 2 = 1 := by simp

/-! ## Crispness -/

theorem evens_crisp : Crisp evens := by
  intro i; fin_cases i <;> simp [evens]

theorem odds_crisp : Crisp odds := by
  intro i; fin_cases i <;> simp [odds]

/-- `graded` is not crisp: at index `1` its value is `half`, neither `0` nor `1`. -/
theorem graded_not_crisp : ¬ Crisp graded := by
  intro h
  have hmem : graded.mem 1 = half := by simp
  rcases h 1 with h0 | h1
  · have : half.val = (0 : Credence).val := congrArg val (hmem ▸ h0)
    simp only [half_val, zero_val] at this; norm_num at this
  · have : half.val = (1 : Credence).val := congrArg val (hmem ▸ h1)
    simp only [half_val, one_val] at this; norm_num at this

/-! ## Complement Values

`odds` is the complement of `evens` pointwise. -/

theorem compl_evens_eq_odds : compl evens = odds := by
  apply ext_mem
  intro i; fin_cases i <;> simp [evens, odds]

theorem compl_graded_mem :
    ∀ i, (compl graded).mem i = if i = 1 then half else 0 := by
  intro i; fin_cases i <;> simp [graded, liar_fixed_point]

/-! ## Intersection Values

`evens` and `odds` are disjoint: their intersection is empty everywhere. -/

theorem inter_evens_odds_empty : inter evens odds = emptyset := by
  apply ext_mem
  intro i; fin_cases i <;> simp [evens, odds]

theorem inter_evens_graded_mem :
    ∀ i, (inter evens graded).mem i = if i = 1 then 0 else 1 := by
  intro i; fin_cases i <;> simp [evens, graded]

/-! ## Union Values

`evens` and `odds` cover `Fin 3`: their union is the universe. -/

theorem union_evens_odds_univ : union evens odds = univ := by
  apply ext_mem
  intro i; fin_cases i <;> simp [evens, odds]

theorem union_evens_graded_mem :
    ∀ i, (union evens graded).mem i = if i = 1 then half else 1 := by
  intro i; fin_cases i <;> simp [evens, graded, liar_fixed_point]

/-! ## A Subset Relation

`evens` sits inside `graded`: at the shared crisp points both are `1`, and where
`evens` is `0` (index `1`) anything dominates it. -/

theorem evens_subset_graded : evens ⊆ graded := by
  rw [subset_def]
  intro i; fin_cases i <;> simp [evens, graded, le_def, half_val]

end CredSet

end Cred
