/-
  Cred Bridge: LP and K3 Bridge Theorems

  The collapse homomorphism connects [0,1]-valued reasoning to
  three-valued reasoning:
  - LP consequence on {0,1/2,1} is equivalent to positivity consequence on [0,1]
  - K3 consequence on {0,1/2,1} is equivalent to certainty consequence on [0,1]
  - Collapse commutes with formula evaluation, at the value level and at
    the formula level
-/

import Cred.Core.Consequence
import Cred.Collapse.Hom

namespace Cred

open ThreeVal

/-! ## Bridge Theorem: LP ↔ Positivity, K3 ↔ Certainty

The collapse homomorphism connects [0,1]-valued reasoning to three-valued
reasoning. The bridge theorem makes this precise: LP consequence on {0,1/2,1}
is equivalent to positivity consequence on [0,1], and K3 consequence is
equivalent to certainty consequence on [0,1]. -/

/-- LP designation via collapse: collapse(c) is LP-designated iff c > 0. -/
theorem lp_designated_iff_pos (c : Credence) :
    isDesignatedLP (collapse c) ↔ 0 < c.val := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have hzero : c.val = 0 := le_antisymm hle c.nonneg
    have hc : c = 0 := by ext; exact hzero
    rw [hc, collapse_zero] at h
    exact h
  · intro hpos
    by_cases h1 : c.val = 1
    · have hc : c = 1 := by ext; exact h1
      rw [hc, collapse_one]
      trivial
    · have h0 : c.val ≠ 0 := ne_of_gt hpos
      rw [collapse_interior c h0 h1]
      trivial

/-- K3 designation via collapse: collapse(c) is K3-designated iff c = 1. -/
theorem k3_designated_iff_one (c : Credence) :
    isDesignatedK3 (collapse c) ↔ c = 1 := by
  constructor
  · intro h
    by_cases h0 : c.val = 0
    · have hc : c = 0 := by ext; exact h0
      rw [hc, collapse_zero] at h; exact absurd h id
    · by_cases h1 : c.val = 1
      · ext; exact h1
      · rw [collapse_interior c h0 h1] at h; exact absurd h id
  · intro h
    rw [h, collapse_one]
    trivial

/-- Lift a ThreeVal to a Credence: zero ↦ 0, half ↦ 1/2, one ↦ 1. -/
noncomputable def liftThreeVal : ThreeVal → Credence
  | ThreeVal.zero => 0
  | ThreeVal.half => Credence.half
  | ThreeVal.one => 1

/-- Lifting then collapsing is the identity. -/
@[simp] theorem lift_collapse_id (v : ThreeVal) :
    collapse (liftThreeVal v) = v := by
  cases v with
  | zero => simp [liftThreeVal, collapse_zero]
  | half => simp [liftThreeVal, collapse_half]
  | one => simp [liftThreeVal, collapse_one]

/-- Lifted LP-designated values have positive credence. -/
theorem lift_pos_of_designated_lp (v : ThreeVal) (h : isDesignatedLP v) :
    0 < (liftThreeVal v).val := by
  cases v with
  | zero => exact absurd h id
  | half => simp [liftThreeVal, Credence.half_val]
  | one => simp [liftThreeVal, Credence.one_val]

/-- Lifted K3-designated values are certain. -/
theorem lift_one_of_designated_k3 (v : ThreeVal) (h : isDesignatedK3 v) :
    liftThreeVal v = 1 := by
  cases v with
  | zero => exact absurd h id
  | half => exact absurd h id
  | one => rfl

/-- Bridge Theorem (LP): LP consequence on {0,1/2,1} is equivalent to
    positivity consequence on [0,1]. -/
theorem lp_bridge (α : Type*) (premises : List α) (conclusion : α) :
    threeValConsequence isDesignatedLP α premises conclusion ↔
    positivityConsequence α premises conclusion := by
  constructor
  · intro hlp v hprem
    let w : ThreeValuation α := fun a => collapse (v a)
    have hwprem : ∀ p ∈ premises, isDesignatedLP (w p) :=
      fun p hp => (lp_designated_iff_pos (v p)).mpr (hprem p hp)
    have := hlp w hwprem
    exact (lp_designated_iff_pos (v conclusion)).mp this
  · intro hpos w hwprem
    let v : α → Credence := fun a => liftThreeVal (w a)
    have hvprem : ∀ p ∈ premises, 0 < (v p).val :=
      fun p hp => lift_pos_of_designated_lp (w p) (hwprem p hp)
    have hcpos := hpos v hvprem
    have : isDesignatedLP (collapse (v conclusion)) :=
      (lp_designated_iff_pos (v conclusion)).mpr hcpos
    rwa [lift_collapse_id] at this

/-- Bridge Theorem (K3): K3 consequence on {0,1/2,1} is equivalent to
    certainty consequence on [0,1]. -/
theorem k3_bridge (α : Type*) (premises : List α) (conclusion : α) :
    threeValConsequence isDesignatedK3 α premises conclusion ↔
    certaintyConsequence α premises conclusion := by
  constructor
  · intro hk3 v hprem
    let w : ThreeValuation α := fun a => collapse (v a)
    have hwprem : ∀ p ∈ premises, isDesignatedK3 (w p) :=
      fun p hp => (k3_designated_iff_one (v p)).mpr (hprem p hp)
    have := hk3 w hwprem
    exact ((k3_designated_iff_one (v conclusion)).mp this)
  · intro hcert w hwprem
    let v : α → Credence := fun a => liftThreeVal (w a)
    have hvprem : ∀ p ∈ premises, v p = 1 :=
      fun p hp => lift_one_of_designated_k3 (w p) (hwprem p hp)
    have hcone := hcert v hvprem
    have : isDesignatedK3 (collapse (v conclusion)) :=
      (k3_designated_iff_one (v conclusion)).mpr hcone
    rwa [lift_collapse_id] at this

/-! ## Collapse Commutes with Formula Evaluation -/

/-- Collapsing after credence evaluation equals three-valued evaluation
    under the collapsed assignment. -/
theorem collapse_eval_eq (v : α → Credence) (φ : Formula α) :
    collapse (evalCred v φ) = evalThreeVal (collapse ∘ v) φ := by
  induction φ with
  | atom a => simp [evalCred, evalThreeVal]
  | neg φ ih => simp only [evalCred, evalThreeVal]; rw [collapse_neg, ih]
  | conj φ ψ ih1 ih2 => simp only [evalCred, evalThreeVal]; rw [collapse_conj, ih1, ih2]
  | disj φ ψ ih1 ih2 => simp only [evalCred, evalThreeVal]; rw [collapse_disj, ih1, ih2]

/-- Three-valued evaluation equals collapse of credence evaluation on lifted atoms. -/
theorem lift_eval_eq (w : α → ThreeVal) (φ : Formula α) :
    evalThreeVal w φ = collapse (evalCred (liftThreeVal ∘ w) φ) := by
  rw [collapse_eval_eq]
  congr 1
  ext a
  simp [Function.comp, lift_collapse_id]

/-! ### Formula-Level Bridge Theorems -/

/-- Formula-level LP bridge: LP formula consequence ↔ formula positivity. -/
theorem lp_formula_bridge (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) :
    formulaConsequence isDesignatedLP α premises conclusion ↔
    formulaPositivity α premises conclusion := by
  constructor
  · intro hlp v hprem
    let w : α → ThreeVal := collapse ∘ v
    have hwprem : ∀ p ∈ premises, isDesignatedLP (evalThreeVal w p) := by
      intro p hp
      rw [← collapse_eval_eq]
      exact (lp_designated_iff_pos _).mpr (hprem p hp)
    have := hlp w hwprem
    rw [← collapse_eval_eq] at this
    exact (lp_designated_iff_pos _).mp this
  · intro hpos w hwprem
    let v : α → Credence := liftThreeVal ∘ w
    have hvprem : ∀ p ∈ premises, 0 < (evalCred v p).val := by
      intro p hp
      have hd := hwprem p hp
      rw [lift_eval_eq] at hd
      exact (lp_designated_iff_pos _).mp hd
    have hcpos := hpos v hvprem
    rw [lift_eval_eq]
    exact (lp_designated_iff_pos _).mpr hcpos

/-- Formula-level K3 bridge: K3 formula consequence ↔ formula certainty. -/
theorem k3_formula_bridge (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) :
    formulaConsequence isDesignatedK3 α premises conclusion ↔
    formulaCertainty α premises conclusion := by
  constructor
  · intro hk3 v hprem
    let w : α → ThreeVal := collapse ∘ v
    have hwprem : ∀ p ∈ premises, isDesignatedK3 (evalThreeVal w p) := by
      intro p hp
      rw [← collapse_eval_eq]
      exact (k3_designated_iff_one _).mpr (hprem p hp)
    have := hk3 w hwprem
    rw [← collapse_eval_eq] at this
    exact (k3_designated_iff_one _).mp this
  · intro hcert w hwprem
    let v : α → Credence := liftThreeVal ∘ w
    have hvprem : ∀ p ∈ premises, evalCred v p = 1 := by
      intro p hp
      have hd := hwprem p hp
      rw [lift_eval_eq] at hd
      exact (k3_designated_iff_one _).mp hd
    have hcone := hcert v hvprem
    rw [lift_eval_eq]
    exact (k3_designated_iff_one _).mpr hcone

end Cred
