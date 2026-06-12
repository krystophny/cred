/-
  Cred Approx: Structure Preservation (shared abstraction)

  A structure on a carrier `X` is given by a credence-valued score
  `P : X → Credence`. `StructureDegree P x` is that score; exact preservation
  is the score-one class. A threshold `t` relaxes exactness to `t ≤ score`.
  `crispScore` lifts a decidable predicate to a 0/1 score, so classical
  structures embed as the boundary case. A self-map `Φ : X → X` preserves a
  structure if it keeps the exact-preservation class.

  This module is the shared abstraction imported by the example modules.
-/

import Cred.Core.Value

namespace Cred

namespace Approx

open Credence

/-! ## Structure degree and preservation classes -/

/-- The degree to which `x` carries the structure `P`. -/
def StructureDegree {X : Type*} (P : X → Credence) (x : X) : Credence := P x

/-- `x` exactly preserves the structure: its degree is certainty. -/
def ExactPreserves {X : Type*} (P : X → Credence) (x : X) : Prop :=
  StructureDegree P x = 1

/-- `x` preserves the structure to at least threshold `t`. -/
def PreservesAt {X : Type*} (t : Credence) (P : X → Credence) (x : X) : Prop :=
  t ≤ StructureDegree P x

/-- An admissible approximation at threshold `t`: preservation up to `t`. -/
def AdmissibleApprox {X : Type*} (t : Credence) (P : X → Credence) (x : X) : Prop :=
  PreservesAt t P x

/-- 0/1 structure score from a decidable predicate. -/
def crispScore {X : Type*} (P : X → Prop) [DecidablePred P] (x : X) : Credence :=
  if P x then 1 else 0

/-- A self-map preserves a structure if it keeps the exact-preservation class. -/
def Preserves {X : Type*} (P : X → Credence) (Φ : X → X) : Prop :=
  ∀ x, ExactPreserves P x → ExactPreserves P (Φ x)

/-! ## Simp lemmas -/

@[simp] theorem StructureDegree_def {X : Type*} (P : X → Credence) (x : X) :
    StructureDegree P x = P x := rfl

@[simp] theorem ExactPreserves_def {X : Type*} (P : X → Credence) (x : X) :
    ExactPreserves P x ↔ P x = 1 := Iff.rfl

@[simp] theorem PreservesAt_def {X : Type*} (t : Credence) (P : X → Credence) (x : X) :
    PreservesAt t P x ↔ t ≤ P x := Iff.rfl

@[simp] theorem AdmissibleApprox_def {X : Type*} (t : Credence) (P : X → Credence) (x : X) :
    AdmissibleApprox t P x ↔ t ≤ P x := Iff.rfl

/-- 0 and 1 are distinct credences (used to read off crisp scores). -/
theorem zero_ne_one_credence : (0 : Credence) ≠ 1 := by
  intro h
  have : (0 : ℝ) = 1 := by simpa using congrArg val h
  exact zero_ne_one this

@[simp] theorem crispScore_one_iff {X : Type*} (P : X → Prop) [DecidablePred P] (x : X) :
    crispScore P x = 1 ↔ P x := by
  unfold crispScore
  by_cases h : P x
  · simp [h]
  · simp only [h, if_false, iff_false]
    exact zero_ne_one_credence

@[simp] theorem crispScore_zero_iff {X : Type*} (P : X → Prop) [DecidablePred P] (x : X) :
    crispScore P x = 0 ↔ ¬ P x := by
  unfold crispScore
  by_cases h : P x
  · simp only [h, if_true, not_true, iff_false]
    intro heq
    exact zero_ne_one_credence heq.symm
  · simp [h]

/-! ## Generic facts -/

/-- Exact preservation of a crisp structure is exactly the predicate. -/
theorem exactPreserves_crispScore {X : Type*} (P : X → Prop) [DecidablePred P] (x : X) :
    ExactPreserves (crispScore P) x ↔ P x := by
  simp

/-- Everything preserves a structure at the zero threshold. -/
theorem preservesAt_zero {X : Type*} (P : X → Credence) (x : X) :
    PreservesAt 0 P x := by
  simpa using zero_le (P x)

/-- Exact preservation is preservation at the top threshold. -/
theorem exactPreserves_iff_preservesAt_one {X : Type*} (P : X → Credence) (x : X) :
    ExactPreserves P x ↔ PreservesAt 1 P x := by
  simp only [ExactPreserves_def, PreservesAt_def]
  constructor
  · intro h; rw [h]
  · intro h; exact le_antisymm (le_one' (P x)) h

/-- Exact preservation strengthens to preservation at any threshold. -/
theorem preservesAt_of_exactPreserves {X : Type*} (t : Credence) (P : X → Credence) (x : X)
    (h : ExactPreserves P x) : PreservesAt t P x := by
  simp only [PreservesAt_def]
  rw [(ExactPreserves_def P x).mp h]
  exact le_one' t

/-- Lower thresholds are easier to meet. -/
theorem preservesAt_mono {X : Type*} {s t : Credence} (hst : s ≤ t) (P : X → Credence) (x : X)
    (h : PreservesAt t P x) : PreservesAt s P x :=
  le_trans hst h

/-- The identity scheme preserves every structure. -/
theorem preserves_id {X : Type*} (P : X → Credence) : Preserves P (id) :=
  fun _ h => h

/-- Preservation is closed under composition of schemes. -/
theorem preserves_comp {X : Type*} (P : X → Credence) {Φ Ψ : X → X}
    (hΦ : Preserves P Φ) (hΨ : Preserves P Ψ) : Preserves P (Ψ ∘ Φ) :=
  fun x hx => hΨ (Φ x) (hΦ x hx)

end Approx

end Cred
