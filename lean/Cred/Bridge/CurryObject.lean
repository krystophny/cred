/-
  Cred Bridge: Curry as an Object

  Curry.lean blocks MP + CP + contraction by exhibiting one bad residuum row.
  Here the block becomes object-facing: the would-be internal conditional,
  bundled as a structure, is empty. The Curry derivation itself appears as a
  lemma: a fixed point c = (c → b) plus a single contraction instance forces
  the arbitrary conclusion b to certainty, and a Curry sentence targeting
  falsum has no solution at all.
-/

import Cred.Bridge.Curry

namespace Cred

namespace Credence

/-! ## The Internal Conditional as an Object -/

/-- The object Curry needs: a total internal conditional on credences with
modus ponens, conditional proof, and contraction. -/
structure InternalConditional where
  arrow : Credence → Credence → Credence
  mp : MP arrow
  cp : CP arrow
  contraction : Contraction arrow

theorem InternalConditional.elim (f : InternalConditional) : False :=
  curry_block ⟨f.arrow, f.mp, f.cp, f.contraction⟩

instance : IsEmpty InternalConditional :=
  ⟨InternalConditional.elim⟩

/-- Object-facing Curry block: no internal conditional exists. -/
theorem no_internal_conditional : ¬ Nonempty InternalConditional := by
  rintro ⟨f⟩
  exact f.elim

/-- Unbundled form: any candidate arrow satisfying the three Curry rules
inhabits the empty structure. -/
theorem mp_cp_contraction_impossible (f : Credence → Credence → Credence)
    (hmp : MP f) (hcp : CP f) (hcontr : Contraction f) : False :=
  InternalConditional.elim ⟨f, hmp, hcp, hcontr⟩

/-! ## Curry Sentences -/

/-- A Curry sentence for arrow `f` and conclusion `b`: a credence equal to
its own conditional `f c b`. -/
def CurryFixedPoint (f : Credence → Credence → Credence)
    (b c : Credence) : Prop :=
  c = f c b

theorem curryFixedPoint_def (f : Credence → Credence → Credence)
    (b c : Credence) : CurryFixedPoint f b c ↔ c = f c b := Iff.rfl

/-- CP alone makes self-implication certain. -/
theorem cp_self_eq_one (f : Credence → Credence → Credence) (hcp : CP f)
    (c : Credence) : f c c = 1 := by
  apply le_antisymm
  · rw [le_def, one_val]
    exact (f c c).le_one
  · exact hcp c c 1 (by simp [le_def])

/-- The Curry derivation: a fixed point plus one contraction instance at it
already forces the arbitrary conclusion to certainty. -/
theorem curry_fixed_point_forces_conclusion
    (f : Credence → Credence → Credence) (hmp : MP f) (hcp : CP f)
    {b c : Credence} (hfix : CurryFixedPoint f b c)
    (hcontr : f c (f c b) ≤ f c b) : b = 1 := by
  have hfix' : c = f c b := hfix
  have hone : (1 : Credence) ≤ f c b := by
    calc (1 : Credence) = f c c := (cp_self_eq_one f hcp c).symm
      _ = f c (f c b) := congrArg (f c) hfix'
      _ ≤ f c b := hcontr
  have hc1 : c = 1 := by
    apply le_antisymm
    · rw [le_def, one_val]
      exact c.le_one
    · rw [hfix']
      exact hone
  have hmpb := hmp c b
  rw [← hfix', hc1] at hmpb
  apply le_antisymm
  · rw [le_def, one_val]
    exact b.le_one
  · simpa using hmpb

/-- Contrapositive: a Curry sentence for an uncertain conclusion refutes the
contraction instance at that sentence. -/
theorem curry_fixed_point_blocks_contraction
    (f : Credence → Credence → Credence) (hmp : MP f) (hcp : CP f)
    {b c : Credence} (hfix : CurryFixedPoint f b c) (hb : b ≠ 1) :
    ¬ f c (f c b) ≤ f c b :=
  fun hcontr => hb (curry_fixed_point_forces_conclusion f hmp hcp hfix hcontr)

/-! ## Curry Sentences Exist, So Contraction Cannot -/

private theorem prodResid_fixed_point_pos {b c : Credence}
    (hc : c = prodResid c b) : 0 < c.val := by
  by_contra hneg
  push_neg at hneg
  have hc0 : c = 0 := by
    ext
    exact le_antisymm hneg c.nonneg
  rw [hc0, prodResid_zero_left] at hc
  have hval := congrArg Credence.val hc
  norm_num at hval

/-- Every positive conclusion has a Curry sentence for any MP + CP arrow,
inherited from the residuum's fixed point at √b. -/
theorem curry_fixed_point_exists
    (f : Credence → Credence → Credence) (hmp : MP f) (hcp : CP f)
    {b : Credence} (hb : 0 < b.val) :
    ∃ c, CurryFixedPoint f b c := by
  obtain ⟨c, hc⟩ := curry_fixed_point_positive b hb
  have hcpos := prodResid_fixed_point_pos hc
  refine ⟨c, ?_⟩
  show c = f c b
  rw [prodResid_unique_positive f hmp hcp c b hcpos]
  exact hc

/-- Any MP + CP arrow carries a Curry sentence whose contraction instance
fails, for every uncertain positive conclusion. -/
theorem curry_sentence_blocks_contraction
    (f : Credence → Credence → Credence) (hmp : MP f) (hcp : CP f)
    {b : Credence} (hb : 0 < b.val) (hb1 : b ≠ 1) :
    ∃ c, CurryFixedPoint f b c ∧ ¬ f c (f c b) ≤ f c b := by
  obtain ⟨c, hfix⟩ := curry_fixed_point_exists f hmp hcp hb
  exact ⟨c, hfix, curry_fixed_point_blocks_contraction f hmp hcp hfix hb1⟩

/-- Arbitrary-conclusion derivation: full contraction would make every
positive credence certain, the structure `InternalConditional` cannot have. -/
theorem contraction_forces_explosion
    (f : Credence → Credence → Credence) (hmp : MP f) (hcp : CP f)
    (hcontr : Contraction f) :
    ∀ b : Credence, 0 < b.val → b = 1 := by
  intro b hb
  obtain ⟨c, hfix⟩ := curry_fixed_point_exists f hmp hcp hb
  exact curry_fixed_point_forces_conclusion f hmp hcp hfix (hcontr c b)

/-! ## Falsum Is Doubly Blocked -/

/-- Targeting falsum, the Curry sentence itself has no solution: MP and CP
alone already close the explosion route at 0. -/
theorem curry_falsum_no_fixed_point
    (f : Credence → Credence → Credence) (hmp : MP f) (hcp : CP f) :
    ¬ ∃ c, CurryFixedPoint f 0 c := by
  rintro ⟨c, hc⟩
  have hc' : c = f c 0 := hc
  by_cases hcz : c.val = 0
  · have hone : (1 : Credence) ≤ f c 0 := hcp c 0 1 (by simp [le_def, hcz])
    rw [← hc'] at hone
    rw [le_def, one_val, hcz] at hone
    linarith
  · have hcpos : 0 < c.val := lt_of_le_of_ne c.nonneg (Ne.symm hcz)
    have hagree : f c 0 = prodResid c 0 :=
      prodResid_unique_positive f hmp hcp c 0 hcpos
    exact curry_no_fixed_point_zero ⟨c, hc'.trans hagree⟩

end Credence

end Cred
