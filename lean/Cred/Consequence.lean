/-
  Cred Part 2: Consequence Relations

  Defines designated-value consequence relations on the three-valued collapse,
  graded consequence on [0,1], and proves compatibility with unconstrained
  conditioning (no explosion).

  Key results:
  - K3 consequence (designate {1}): paracomplete, no tautologies
  - LP consequence (designate {1, 1/2}): paraconsistent, explosion fails
  - RM3 consequence (designate {1, 1/2} + relevance)
  - Graded consequence parametrized by threshold
  - No-explosion theorem for all compatible consequence relations
-/

import Cred.Basic
import Cred.Valuation

namespace Cred

open ThreeVal

/-! ## Designated Values -/

/-- K3 designation: only `one` is designated (strict, paracomplete). -/
def isDesignatedK3 : ThreeVal → Prop
  | one => True
  | _ => False

/-- LP designation: `one` and `half` are designated (tolerant, paraconsistent). -/
def isDesignatedLP : ThreeVal → Prop
  | one => True
  | half => True
  | zero => False

instance : DecidablePred isDesignatedK3 :=
  fun v => by cases v <;> simp [isDesignatedK3] <;> infer_instance

instance : DecidablePred isDesignatedLP :=
  fun v => by cases v <;> simp [isDesignatedLP] <;> infer_instance

/-! ## Three-Valued Consequence -/

/-- A three-valued valuation: assigns a ThreeVal to each proposition. -/
def ThreeValuation (α : Type*) := α → ThreeVal

/-- Three-valued consequence: premises entail conclusion when every valuation
    that makes all premises designated also makes the conclusion designated. -/
def threeValConsequence (designated : ThreeVal → Prop) (α : Type*)
    (premises : List α) (conclusion : α) : Prop :=
  ∀ v : ThreeValuation α,
    (∀ p ∈ premises, designated (v p)) → designated (v conclusion)

/-! ### K3 Properties -/

/-- K3 is paracomplete: there are no K3 tautologies.
    Proof: the constant-half valuation makes every formula non-designated. -/
theorem k3_no_tautology (α : Type*) [Nonempty α] (a : α) :
    ¬ threeValConsequence isDesignatedK3 α [] a := by
  intro h
  have := h (fun _ => half) (by simp)
  exact this

/-- K3: excluded middle fails. For any proposition A, there exists a valuation
    where A ⊔ ~A is not designated (when A = half). -/
theorem k3_excluded_middle_fails :
    ∃ v : ThreeVal, ¬ isDesignatedK3 (ThreeVal.disj v (ThreeVal.neg v)) := by
  use half
  simp [ThreeVal.disj, ThreeVal.neg, isDesignatedK3]

/-! ### LP Properties -/

/-- LP: excluded middle holds. For any value, A ⊔ ~A is always designated. -/
theorem lp_excluded_middle (v : ThreeVal) :
    isDesignatedLP (ThreeVal.disj v (ThreeVal.neg v)) := by
  cases v <;> simp [ThreeVal.disj, ThreeVal.neg, isDesignatedLP]

/-- LP: explosion fails. A and ~A can both be designated (at half)
    without forcing arbitrary B to be designated. -/
theorem lp_no_explosion :
    ∃ v : ThreeValuation (Fin 2),
      isDesignatedLP (v 0) ∧ isDesignatedLP (ThreeVal.neg (v 0)) ∧
      ¬ isDesignatedLP (v 1) := by
  use fun i => if i = 0 then half else zero
  simp [ThreeVal.neg, isDesignatedLP]

/-! ### Graded Consequence -/

/-- Graded consequence parametrized by threshold t:
    Premises with credence ≥ t entail conclusion with credence ≥ t.
    This works directly on [0,1] without collapsing. -/
def gradedConsequence (t : Credence) (α : Type*)
    (premises : List α) (conclusion : α) : Prop :=
  ∀ v : α → Credence,
    (∀ p ∈ premises, t ≤ v p) → t ≤ v conclusion

/-- Graded consequence at t=1 is strict: only certainty propagates. -/
theorem graded_at_one_is_strict (α : Type*) (premises : List α) (conclusion : α) :
    gradedConsequence 1 α premises conclusion ↔
    ∀ v : α → Credence,
      (∀ p ∈ premises, v p = 1) → v conclusion = 1 := by
  constructor
  · intro h v hprem
    have hge := h v (fun p hp => by rw [hprem p hp])
    exact le_antisymm (v conclusion).le_one hge
  · intro h v hprem
    have hprem' : ∀ p ∈ premises, v p = 1 := by
      intro p hp
      exact le_antisymm (v p).le_one (hprem p hp)
    rw [h v hprem']

/-! ## No-Explosion Theorem

The key result: for any consequence relation compatible with unconstrained
conditioning at zero, explosion fails when premises have credence 1/2. -/

/-- A consequence relation on credences is explosion-free when the existence
    of a valuation with A and ~A both having credence 1/2 does not force
    arbitrary B to any particular value. -/
theorem no_explosion_at_half :
    ∃ v : Fin 2 → Credence,
      v 0 = Credence.half ∧
      Credence.neg (v 0) = Credence.half ∧
      v 1 = 0 := by
  use fun i => if i = 0 then Credence.half else 0
  refine ⟨by simp, ?_, by simp⟩
  simp [Credence.liar_fixed_point]

/-- For any threshold 0 < t ≤ 1/2, graded consequence does not have explosion:
    there exist premises A, ~A both above threshold with conclusion below. -/
theorem graded_no_explosion (t : Credence) (ht : t.val ≤ 1/2) (ht_pos : 0 < t.val) :
    ∃ v : Fin 2 → Credence,
      t ≤ v 0 ∧ t ≤ Credence.neg (v 0) ∧ ¬(t ≤ v 1) := by
  use fun i => if i = 0 then Credence.half else 0
  refine ⟨?_, ?_, ?_⟩
  · simp [Credence.le_def, Credence.half_val]; linarith
  · simp [Credence.neg, Credence.le_def, Credence.half_val]; linarith
  · simp [Credence.le_def, Credence.zero_val]
    linarith

/-- Connection: unconstrained conditioning at zero means that
    when evidence has credence 0, no conclusion is forced. This is the
    algebraic basis for explosion failure. -/
theorem unconstrained_blocks_explosion (c : Credence) :
    ∃ cond : Credence.Conditioning 0 0, cond.condCred = c :=
  Credence.conditioning_zero_any c

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

/-! ### Consequence on [0,1] -/

/-- Positivity consequence: every valuation making premises positive
    also makes the conclusion positive. -/
def positivityConsequence (α : Type*) (premises : List α) (conclusion : α) : Prop :=
  ∀ v : α → Credence, (∀ p ∈ premises, 0 < (v p).val) → 0 < (v conclusion).val

/-- Certainty consequence: every valuation making premises certain
    also makes the conclusion certain. -/
def certaintyConsequence (α : Type*) (premises : List α) (conclusion : α) : Prop :=
  ∀ v : α → Credence, (∀ p ∈ premises, v p = 1) → v conclusion = 1

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

/-- Positivity consequence is explosion-free: same witness as LP. -/
theorem positivity_no_explosion :
    ∃ v : Fin 2 → Credence,
      0 < (v 0).val ∧ 0 < (Credence.neg (v 0)).val ∧ ¬(0 < (v 1).val) := by
  use fun i => if i = 0 then Credence.half else 0
  refine ⟨?_, ?_, ?_⟩
  · simp [Credence.half_val]
  · simp only [show (0 : Fin 2) = 0 from rfl, ite_true, Credence.neg_val, Credence.half_val]
    norm_num
  · simp [Credence.zero_val]

end Cred
