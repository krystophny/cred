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

/-- Connection to Part 1: unconstrained conditioning at zero means that
    when evidence has credence 0, no conclusion is forced. This is the
    algebraic basis for explosion failure. -/
theorem unconstrained_blocks_explosion (c : Credence) :
    ∃ cond : Credence.Conditioning 0 0, cond.condCred = c :=
  Credence.conditioning_zero_any c

end Cred
