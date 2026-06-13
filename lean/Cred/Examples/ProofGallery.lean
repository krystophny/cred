/-
  Cred Examples: a proof gallery across the binary, ternary, and continuous
  layers (issue #651).

  Three bundling theorems collect already-proved anchors from the existing
  example and bridge modules, one per layer:

  - Binary: the four-world truth-set model. Entailment is truth-set inclusion,
    `A` entails the tautology `C`, but `A` does not entail `B`.
  - Ternary: the LP/K3 collapse bridges (LP = positivity, K3 = certainty) and
    LP paraconsistency (explosion fails at the half value).
  - Continuous: the worked robust-conditioning instance. Conditioning the
    Fréchet joint band on positive evidence yields a conditional band that is
    robust below a low threshold and dependence-sensitive at a high one.

  Each gallery theorem is a conjunction of the reused facts; no new content,
  only a stable bundling the paper can cite.
-/

import Cred.Examples.FiniteWorlds
import Cred.Examples.RobustConditioning
import Cred.Bridge.LPK3

namespace Cred.Examples.ProofGallery

/-! ## Binary layer -/

/-- Binary truth-set gallery: entailment is truth-set inclusion, `A` entails the
    tautology `C`, and `A` does not entail `B`. -/
theorem binary_truthset_proof_gallery :
    (∀ A B : FiniteWorlds.BoolProp,
        FiniteWorlds.Entails A B ↔ FiniteWorlds.truthSet A ⊆ FiniteWorlds.truthSet B) ∧
      FiniteWorlds.Entails FiniteWorlds.A FiniteWorlds.C ∧
      ¬ FiniteWorlds.Entails FiniteWorlds.A FiniteWorlds.B :=
  ⟨FiniteWorlds.entails_iff_subset, FiniteWorlds.A_entails_C, FiniteWorlds.A_not_entails_B⟩

/-! ## Ternary layer -/

/-- Ternary gallery: the LP and K3 collapse bridges hold for all formula
    consequences, and LP explosion fails (a paraconsistent witness). -/
theorem ternary_proof_gallery :
    (∀ (α : Type) (premises : List (Cred.Formula α)) (conclusion : Cred.Formula α),
        Cred.formulaConsequence Cred.isDesignatedLP α premises conclusion ↔
          Cred.formulaPositivity α premises conclusion) ∧
      (∀ (α : Type) (premises : List (Cred.Formula α)) (conclusion : Cred.Formula α),
        Cred.formulaConsequence Cred.isDesignatedK3 α premises conclusion ↔
          Cred.formulaCertainty α premises conclusion) ∧
      (∃ v : Cred.ThreeValuation (Fin 2),
        Cred.isDesignatedLP (v 0) ∧ Cred.isDesignatedLP (Cred.ThreeVal.neg (v 0)) ∧
          ¬ Cred.isDesignatedLP (v 1)) :=
  ⟨fun α => Cred.lp_formula_bridge α, fun α => Cred.k3_formula_bridge α,
    Cred.lp_no_explosion⟩

/-! ## Continuous layer -/

/-- Continuous gallery: the evidence is positive, the conditional band derived
    from the Fréchet joint band is `[3/7, 6/7]`, it is robust at the low
    threshold `1/3`, and dependence-sensitive at the high threshold `4/5`. -/
theorem continuous_proof_gallery :
    0 < RobustConditioning.b.val ∧
      ((3 / 10 : ℝ) / RobustConditioning.b.val = 3 / 7 ∧
        (3 / 5 : ℝ) / RobustConditioning.b.val = 6 / 7) ∧
      ((1 / 3 : ℝ) ≤ 3 / 7 ∧ (1 / 3 : ℝ) ≤ 6 / 7) ∧
      ((3 / 7 : ℝ) < 4 / 5 ∧ (4 / 5 : ℝ) < 6 / 7) :=
  ⟨RobustConditioning.b_pos, RobustConditioning.cond_interval,
    RobustConditioning.robust_at_low_threshold,
    RobustConditioning.sensitive_at_high_threshold⟩

end Cred.Examples.ProofGallery
