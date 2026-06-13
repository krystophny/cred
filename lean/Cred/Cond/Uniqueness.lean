/-
  Cred Cond: Uniqueness of the Chain-Rule Conditional Semantics (#656)

  The admissible-set conditioning `Cond j e` (Cred.Cond.Admissible) is the
  solution set of the chain rule `c ⊗ e = j`. This module shows that this
  set-valued semantics is forced: any set-valued conditional semantics
  `S : Credence → Credence → Set Credence` that is CHAIN-RULE FAITHFUL,
  meaning `c ∈ S j e ↔ c ⊗ e = j`, must equal `Cond` pointwise.

  Faithfulness is the definitional content of `Cond` itself, so the proof is
  pure set extensionality. The trichotomy consequences (singleton at positive
  evidence, full set at zero/zero, empty at incoherent pairs) then transfer to
  any faithful semantics by rewriting through `chainRuleFaithful_eq_Cond`.
-/

import Cred.Cond.Admissible

namespace Cred

namespace Credence

/-! ## Chain-Rule Faithfulness -/

/--
A set-valued conditional semantics is CHAIN-RULE FAITHFUL when, for every joint
`j` and evidence `e`, its admissible conditionals are exactly the solutions of
the chain rule `c ⊗ e = j`.
-/
def ChainRuleFaithful (S : Credence → Credence → Set Credence) : Prop :=
  ∀ j e c : Credence, c ∈ S j e ↔ c ⊗ e = j

/-- `Cond` is itself chain-rule faithful: membership is the chain rule by definition. -/
theorem cond_chainRuleFaithful : ChainRuleFaithful Cond := by
  intro j e c
  rfl

/--
Uniqueness: any chain-rule-faithful set-valued conditional semantics equals the
admissible set `Cond` at every joint/evidence pair. The shape of the conditional
fiber is fully determined by the chain rule.
-/
theorem chainRuleFaithful_eq_Cond (S : Credence → Credence → Set Credence)
    (hS : ChainRuleFaithful S) (j e : Credence) : S j e = Cond j e := by
  ext c
  rw [hS j e c]
  rfl

/-! ## Trichotomy Consequences for Any Faithful Semantics

Each statement transfers a fiber-shape fact of `Cond` to an arbitrary faithful
`S` by rewriting through `chainRuleFaithful_eq_Cond`. -/

/--
Positive evidence pins a faithful semantics to a singleton: the unique
conditional credence `j/e` constructed by `conditioning_mk`.
-/
theorem uniqueness_positive (S : Credence → Credence → Set Credence)
    (hS : ChainRuleFaithful S) (j e : Credence) (he : 0 < e.val)
    (hle : j.val ≤ e.val) :
    S j e = {(conditioning_mk j e he hle).condCred} := by
  rw [chainRuleFaithful_eq_Cond S hS j e]
  exact cond_singleton_of_pos j e he hle

/--
Zero evidence with zero joint admits every credence in a faithful semantics.
-/
theorem uniqueness_zero (S : Credence → Credence → Set Credence)
    (hS : ChainRuleFaithful S) : S 0 0 = Set.univ := by
  rw [chainRuleFaithful_eq_Cond S hS 0 0]
  exact cond_zero_zero_univ

/--
Incoherent pairs `j > e` admit no conditional in a faithful semantics: the
fiber is empty.
-/
theorem uniqueness_incoherent (S : Credence → Credence → Set Credence)
    (hS : ChainRuleFaithful S) (j e : Credence) (hgt : e.val < j.val) :
    S j e = ∅ := by
  rw [chainRuleFaithful_eq_Cond S hS j e]
  rw [Set.eq_empty_iff_forall_not_mem]
  intro c hc
  have hle : j.val ≤ e.val :=
    (cond_nonempty_iff j e).mp ⟨c, hc⟩
  exact absurd hle (not_le_of_gt hgt)

end Credence

end Cred
