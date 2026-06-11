/-
  Cred Foundation Quantifiers

  Quantifier rules require `QuantifierLaws`; the raw semantics leaves `all` and
  `ex` as explicit credence operations.
-/

import Cred.Foundation.Equality

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

def QuantifierThresholdConsequence (t : Credence)
    (premises : List (Formula Func Pred)) (conclusion : Formula Func Pred) :
    Prop :=
  ∀ (M : Structure.{u, v, w} Func Pred) (env : M.Assignment),
    M.QuantifierLaws →
    (∀ p ∈ premises, t ≤ M.evalFormula env p) →
    t ≤ M.evalFormula env conclusion

theorem threshold_to_quantifier (t : Credence)
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : ThresholdConsequence.{u, v, w} t Γ φ) :
    QuantifierThresholdConsequence.{u, v, w} t Γ φ := by
  intro M env _ hΓ
  exact h M env hΓ

theorem forall_elim_semantic (t : Credence)
    (M : Structure.{u, v, w} Func Pred) (env : M.Assignment)
    (hQ : M.QuantifierLaws) (φ : Formula Func Pred) (x : M.Domain) :
    t ≤ M.evalFormula env (.forallE φ) →
    t ≤ M.evalFormula (M.update env x) φ := by
  intro hAll
  have hInst := hQ.all_le_instance
    (fun y => M.evalFormula (M.update env y) φ) x
  exact le_trans hAll hInst

theorem exists_intro_semantic (t : Credence)
    (M : Structure.{u, v, w} Func Pred) (env : M.Assignment)
    (hQ : M.QuantifierLaws) (φ : Formula Func Pred) (x : M.Domain) :
    t ≤ M.evalFormula (M.update env x) φ →
    t ≤ M.evalFormula env (.existsE φ) := by
  intro hφ
  have hInst := hQ.instance_le_ex
    (fun y => M.evalFormula (M.update env y) φ) x
  exact le_trans hφ hInst

end Structure

end Foundation
end Cred
