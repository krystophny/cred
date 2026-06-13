/-
  Cred Dependence: Conditioning over Joint Bands (issue #633)

  Connects the imprecise joint band `[jlo, jhi]` to the admissible-set
  conditioning of `Cred.Cond.Admissible`. With positive evidence, each exact
  joint pins a singleton conditional `j / e`; sweeping the joint over the band
  sweeps the conditional over `[jlo/e, jhi/e]`. Robustness and
  dependence-sensitivity of a threshold `t` are read off from where `t` sits in
  that conditional interval.

  Everything reuses `Cond`, `cond_singleton_of_pos`, and `cond_zero_zero_univ`;
  no new conditioning primitive is introduced.
-/

import Cred.Cond.Admissible

namespace Cred

namespace Dependence

open Cred.Credence

/-- The conditional interval swept by joints in the band `[jlo, jhi]` against
    positive evidence `e`: a credence `c` arises as the admissible conditional
    for some joint in the band iff `c.val ∈ [jlo.val / e.val, jhi.val / e.val]`.

    Reuses `cond_singleton_of_pos`: for a fixed joint `j ≤ e` the admissible set
    is the singleton `{j / e}`, so the union over `j ∈ [jlo, jhi]` is exactly
    the value interval `[jlo/e, jhi/e]`. -/
theorem cond_interval_of_pos (e jlo jhi : Credence)
    (he : 0 < e.val) (_hlohi : jlo.val ≤ jhi.val)
    (_hlo_le : jlo.val ≤ e.val) (_hhi_le : jhi.val ≤ e.val) (c : Credence) :
    (∃ j : Credence, jlo.val ≤ j.val ∧ j.val ≤ jhi.val ∧ c ∈ Cond j e)
      ↔ (jlo.val / e.val ≤ c.val ∧ c.val ≤ jhi.val / e.val) := by
  constructor
  · rintro ⟨j, hjlo, hjhi, hcj⟩
    -- membership c ∈ Cond j e means c.val * e.val = j.val
    have hchain : c.val * e.val = j.val := congrArg Credence.val hcj
    have hcval : c.val = j.val / e.val := by
      rw [eq_div_iff (ne_of_gt he)]; exact hchain
    rw [hcval]
    exact ⟨div_le_div_of_nonneg_right hjlo he.le,
           div_le_div_of_nonneg_right hjhi he.le⟩
  · rintro ⟨hlo, hhi⟩
    -- choose j = c ⊗ e; its value is c.val * e.val, which lies in [jlo, jhi]
    refine ⟨c ⊗ e, ?_, ?_, ?_⟩
    · -- jlo.val ≤ c.val * e.val
      have : jlo.val / e.val * e.val ≤ c.val * e.val :=
        mul_le_mul_of_nonneg_right hlo (le_of_lt he)
      rw [div_mul_cancel₀ _ (ne_of_gt he)] at this
      simpa using this
    · -- c.val * e.val ≤ jhi.val
      have : c.val * e.val ≤ jhi.val / e.val * e.val :=
        mul_le_mul_of_nonneg_right hhi (le_of_lt he)
      rw [div_mul_cancel₀ _ (ne_of_gt he)] at this
      simpa using this
    · -- c ∈ Cond (c ⊗ e) e
      show c ⊗ e = c ⊗ e
      rfl

/-- The zero-joint, zero-evidence fiber is unconstrained. Restatement of
    `cond_zero_zero_univ`: conditioning on impossible evidence narrows nothing. -/
theorem cond_fiber_zero : Cond (0 : Credence) (0 : Credence) = Set.univ :=
  cond_zero_zero_univ

/-- Robustness below a threshold: if `t ≤ jlo / e`, then every admissible
    conditional for every joint in the band `[jlo, jhi]` is `≥ t`. The
    conclusion is robust to the unknown dependence. -/
theorem robust_above_threshold (e jlo _jhi t : Credence)
    (he : 0 < e.val)
    (ht : t.val ≤ jlo.val / e.val)
    (c j : Credence) (hjlo : jlo.val ≤ j.val) (hcj : c ∈ Cond j e) :
    t ≤ c := by
  have hchain : c.val * e.val = j.val := congrArg Credence.val hcj
  have hcval : c.val = j.val / e.val := by
    rw [eq_div_iff (ne_of_gt he)]; exact hchain
  rw [le_def, hcval]
  exact le_trans ht (div_le_div_of_nonneg_right hjlo he.le)

/-- Dependence sensitivity: if the threshold `t` lands strictly inside the
    conditional interval (`jlo/e < t ≤ jhi/e`), then some admissible
    conditional drawn from the band falls below `t` and some lands at or above
    `t`. The verdict is not robust: it depends on the supplied joint. -/
theorem dependence_sensitive (e jlo jhi t : Credence)
    (he : 0 < e.val) (hlohi : jlo.val ≤ jhi.val)
    (hhi_le : jhi.val ≤ e.val)
    (hlow : jlo.val / e.val < t.val) (hhigh : t.val ≤ jhi.val / e.val) :
    (∃ clo j, jlo.val ≤ j.val ∧ j.val ≤ jhi.val ∧ clo ∈ Cond j e ∧ clo < t) ∧
    (∃ chi j, jlo.val ≤ j.val ∧ j.val ≤ jhi.val ∧ chi ∈ Cond j e ∧ t ≤ chi) := by
  constructor
  · -- clo = jlo / e, with joint jlo
    refine ⟨conditioning_mk jlo e he (le_trans hlohi hhi_le) |>.condCred, jlo,
      le_refl _, hlohi, ?_, ?_⟩
    · exact (conditioning_mk jlo e he (le_trans hlohi hhi_le)).chainRule
    · rw [lt_def]
      show jlo.val / e.val < t.val
      exact hlow
  · -- chi = jhi / e, with joint jhi
    refine ⟨conditioning_mk jhi e he hhi_le |>.condCred, jhi,
      hlohi, le_refl _, ?_, ?_⟩
    · exact (conditioning_mk jhi e he hhi_le).chainRule
    · rw [le_def]
      show t.val ≤ jhi.val / e.val
      exact hhigh

end Dependence

end Cred
