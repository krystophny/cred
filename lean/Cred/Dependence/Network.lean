/-
  Cred Dependence: networks of three or more propositions (extends issue #633/#638)

  The two-proposition story (`Cred.Examples.FiniteWorlds`) shows that marginals
  do not fix a pairwise joint. This module pushes one level higher: pairwise
  data does not fix the triple joint.

  An eight-world space `W := Fin 8` carries three Boolean propositions whose
  truth values are the three bits of the world index:

      A = bit0,  B = bit1,  C = bit2.

  A weight `μ : W → ℚ` gives `P μ X := ∑ w, if X w then μ w else 0`, an explicit
  `Finset.sum` of rationals (no measure theory). Two weightings `μ1`, `μ2`
  agree on every single marginal `P A, P B, P C` AND every pairwise joint
  `P (A∧B), P (A∧C), P (B∧C)`, yet disagree on the triple joint `P (A∧B∧C)`
  (`triple_joint_not_determined_by_pairwise`). The two weightings differ by the
  parity perturbation `±1/16` on the eight cells: that perturbation cancels in
  every sum that leaves at least one bit free (all marginals and pairwise
  joints) but survives in the single all-true cell `w7`.

  `JointFamily3` records an n-ary (here ternary) supplied-joint policy as a
  predicate on the pairwise-plus-triple data, the three-proposition analogue of
  `Cred.Dependence.JointFamily`.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Cred.Dependence

/-! ## Worlds and the three bit-propositions -/

/-- The eight-world space; world `w` encodes a triple of bits `(A, B, C)`. -/
abbrev W3 := Fin 8

/-- A Boolean proposition over the eight worlds. -/
abbrev BoolProp3 := W3 → Bool

/-- `A` holds at worlds with bit 0 set: `{1,3,5,7}`. -/
def A3 : BoolProp3 := ![false, true, false, true, false, true, false, true]

/-- `B` holds at worlds with bit 1 set: `{2,3,6,7}`. -/
def B3 : BoolProp3 := ![false, false, true, true, false, false, true, true]

/-- `C` holds at worlds with bit 2 set: `{4,5,6,7}`. -/
def C3 : BoolProp3 := ![false, false, false, false, true, true, true, true]

/-- Pointwise conjunction of two propositions over the eight worlds. -/
def conj3 (X Y : BoolProp3) : BoolProp3 := fun w => X w && Y w

/-! ## Probability as an explicit rational sum -/

/-- Probability of a proposition under a rational weighting. -/
def P3 (μ : W3 → ℚ) (X : BoolProp3) : ℚ := ∑ w, if X w then μ w else 0

/-- Baseline uniform weighting `[1/8, …, 1/8]`. -/
def ν1 : W3 → ℚ := ![1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8, 1/8]

/-- Parity-perturbed weighting: each cell shifted by `±1/16` according to the
    parity of its bit pattern (`-` on even-weight cells, `+` on odd). The shifts
    sum to zero and cancel in every marginal and pairwise joint, but not in the
    all-true cell. -/
def ν2 : W3 → ℚ :=
  ![1/8 - 1/16, 1/8 + 1/16, 1/8 + 1/16, 1/8 - 1/16,
    1/8 + 1/16, 1/8 - 1/16, 1/8 - 1/16, 1/8 + 1/16]

/-! ## Both weightings are probability vectors -/

theorem ν1_sum : ∑ w, ν1 w = 1 := by
  simp only [ν1, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

theorem ν2_sum : ∑ w, ν2 w = 1 := by
  simp only [ν2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-! ## Equal single marginals -/

theorem marginal3_A_eq : P3 ν1 A3 = P3 ν2 A3 := by
  simp only [P3, A3, ν1, ν2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

theorem marginal3_B_eq : P3 ν1 B3 = P3 ν2 B3 := by
  simp only [P3, B3, ν1, ν2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

theorem marginal3_C_eq : P3 ν1 C3 = P3 ν2 C3 := by
  simp only [P3, C3, ν1, ν2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-! ## Equal pairwise joints -/

theorem joint3_AB_eq : P3 ν1 (conj3 A3 B3) = P3 ν2 (conj3 A3 B3) := by
  simp only [P3, conj3, A3, B3, ν1, ν2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

theorem joint3_AC_eq : P3 ν1 (conj3 A3 C3) = P3 ν2 (conj3 A3 C3) := by
  simp only [P3, conj3, A3, C3, ν1, ν2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

theorem joint3_BC_eq : P3 ν1 (conj3 B3 C3) = P3 ν2 (conj3 B3 C3) := by
  simp only [P3, conj3, B3, C3, ν1, ν2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-! ## The triple joint differs -/

/-- Under the uniform weighting the triple joint is `1/8`. -/
theorem triple3_ν1 : P3 ν1 (conj3 (conj3 A3 B3) C3) = 1/8 := by
  simp only [P3, conj3, A3, B3, C3, ν1, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-- Under the parity-perturbed weighting the triple joint is `1/8 + 1/16 = 3/16`. -/
theorem triple3_ν2 : P3 ν2 (conj3 (conj3 A3 B3) C3) = 3/16 := by
  simp only [P3, conj3, A3, B3, C3, ν2, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num

/-- Pairwise marginals and pairwise joints do not determine the triple joint:
    two weightings agree on `P A, P B, P C` and on `P (A∧B), P (A∧C), P (B∧C)`,
    yet disagree on `P (A∧B∧C)`. -/
theorem triple_joint_not_determined_by_pairwise :
    P3 ν1 A3 = P3 ν2 A3 ∧
      P3 ν1 B3 = P3 ν2 B3 ∧
      P3 ν1 C3 = P3 ν2 C3 ∧
      P3 ν1 (conj3 A3 B3) = P3 ν2 (conj3 A3 B3) ∧
      P3 ν1 (conj3 A3 C3) = P3 ν2 (conj3 A3 C3) ∧
      P3 ν1 (conj3 B3 C3) = P3 ν2 (conj3 B3 C3) ∧
      P3 ν1 (conj3 (conj3 A3 B3) C3) ≠ P3 ν2 (conj3 (conj3 A3 B3) C3) := by
  refine ⟨marginal3_A_eq, marginal3_B_eq, marginal3_C_eq,
    joint3_AB_eq, joint3_AC_eq, joint3_BC_eq, ?_⟩
  rw [triple3_ν1, triple3_ν2]; norm_num

/-! ## A ternary supplied-joint policy

`JointFamily3` is the three-proposition analogue of
`Cred.Dependence.JointFamily`: a predicate on the supplied pairwise-and-triple
joint data. It records which ternary dependence policies a context admits,
without computing the triple joint from the pairwise data (the theorem above
shows that computation is impossible in general). -/

/-- Ternary supplied-joint data: single marginals, the three pairwise joints,
    and the triple joint, all supplied as rationals. -/
structure TripleContext where
  pa : ℚ
  pb : ℚ
  pc : ℚ
  pab : ℚ
  pac : ℚ
  pbc : ℚ
  pabc : ℚ

/-- A ternary dependence policy as a predicate on triple contexts. -/
def JointFamily3 := TripleContext → Prop

namespace JointFamily3

/-- The full-independence policy: every joint is the product of its marginals. -/
def independence : JointFamily3 := fun Γ =>
  Γ.pab = Γ.pa * Γ.pb ∧ Γ.pac = Γ.pa * Γ.pc ∧ Γ.pbc = Γ.pb * Γ.pc ∧
    Γ.pabc = Γ.pa * Γ.pb * Γ.pc

/-- The trivial policy admitting every supplied triple context. -/
def any : JointFamily3 := fun _ => True

end JointFamily3

/-- The triple context read off the uniform weighting `ν1`. -/
def tripleContextν1 : TripleContext where
  pa := P3 ν1 A3
  pb := P3 ν1 B3
  pc := P3 ν1 C3
  pab := P3 ν1 (conj3 A3 B3)
  pac := P3 ν1 (conj3 A3 C3)
  pbc := P3 ν1 (conj3 B3 C3)
  pabc := P3 ν1 (conj3 (conj3 A3 B3) C3)

/-- The uniform weighting realizes the full-independence policy: all joints are
    products of the `1/2` marginals (`1/4` pairwise, `1/8` triple). -/
theorem tripleContextν1_independence : JointFamily3.independence tripleContextν1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [JointFamily3.independence, tripleContextν1, P3, conj3,
        A3, B3, C3, ν1, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
     norm_num)

end Cred.Dependence
