/-
  Cred Foundation Equality

  Equality rules live above the raw semantics.  They require `CrispEquality`
  because the base structure keeps equality as an explicit credence operation.
-/

import Cred.Foundation.Proof

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

def CrispThresholdConsequence (t : Credence)
    (premises : List (Formula Func Pred)) (conclusion : Formula Func Pred) :
    Prop :=
  ∀ (M : Structure.{u, v, w} Func Pred) (env : M.Assignment),
    M.CrispEquality →
    (∀ p ∈ premises, t ≤ M.evalFormula env p) →
    t ≤ M.evalFormula env conclusion

theorem threshold_to_crisp (t : Credence)
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : ThresholdConsequence.{u, v, w} t Γ φ) :
    CrispThresholdConsequence.{u, v, w} t Γ φ := by
  intro M env _ hΓ
  exact h M env hΓ

theorem equality_reflexivity_threshold (t : Credence) (τ : Term Func) :
    CrispThresholdConsequence.{u, v, w} t
      ([] : List (Formula Func Pred)) (@Formula.equal Func Pred τ τ) := by
  intro M env hEq hΓ
  simp [evalFormula, hEq.eq_refl, Credence.le_one']

inductive CrispDerivation (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Prop where
  | base {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      Derivation t Γ φ → CrispDerivation t Γ φ
  | equalityRefl {Γ : List (Formula Func Pred)} (τ : Term Func) :
      CrispDerivation t Γ (.equal τ τ)

theorem crisp_derivation_sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : CrispDerivation t Γ φ) :
    CrispThresholdConsequence.{u, v, w} t Γ φ := by
  induction h with
  | base h =>
      exact threshold_to_crisp t (derivation_sound h)
  | equalityRefl τ =>
      intro M env hEq hΓ
      simp [evalFormula, hEq.eq_refl, Credence.le_one']

end Structure

end Foundation
end Cred
