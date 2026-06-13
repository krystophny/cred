/-
  Cred ProofTheory: Designation Labels (issues #642, #634)

  A `Label` records the designation status demanded of a credence: positive
  (any nonzero credence), certain (credence 1), or a threshold (credence at
  least `t`).  This is the self-contained label layer for the generative
  labelled calculus.  It mirrors the `LabelKind` of `Cred.Sequent` but stays
  independent of the heavier `Formula`/`Cond` machinery so the generative
  fragment can be read on its own.
-/

import Cred.Core.Value

namespace Cred.ProofTheory

open Cred

/-- The designation status demanded of a credence. -/
inductive Label where
  | positive : Label
  | certain : Label
  | threshold : Credence → Label

namespace Label

/-- When a credence meets the designation demanded by a label.
    - `positive`: strictly above impossibility.
    - `certain`: exactly certainty.
    - `threshold t`: at least `t`. -/
def designates : Label → Credence → Prop
  | positive, c => 0 < c.val
  | certain, c => c.val = 1
  | threshold t, c => t.val ≤ c.val

/-- Certainty designates positivity: a certain credence is positive. -/
theorem certain_designates_positive {c : Credence} (h : designates certain c) :
    designates positive c := by
  simp only [designates] at h ⊢
  rw [h]; norm_num

/-- A certain credence meets every threshold. -/
theorem certain_designates_threshold {c : Credence} (t : Credence)
    (h : designates certain c) : designates (threshold t) c := by
  simp only [designates] at h ⊢
  rw [h]; exact t.le_one

/-- Lowering a threshold preserves designation. -/
theorem threshold_mono {c : Credence} {s t : Credence}
    (h : designates (threshold s) c) (hts : t.val ≤ s.val) :
    designates (threshold t) c := by
  simp only [designates] at h ⊢
  exact le_trans hts h

/-- A strictly positive threshold designates positivity. -/
theorem threshold_designates_positive {c : Credence} {t : Credence}
    (h : designates (threshold t) c) (ht : 0 < t.val) :
    designates positive c := by
  simp only [designates] at h ⊢
  exact lt_of_lt_of_le ht h

/-- Certainty is `threshold 1`. -/
theorem certain_iff_threshold_one {c : Credence} :
    designates certain c ↔ designates (threshold 1) c := by
  simp only [designates, Credence.one_val]
  constructor
  · intro h; rw [h]
  · intro h; exact le_antisymm c.le_one h

end Label

end Cred.ProofTheory
