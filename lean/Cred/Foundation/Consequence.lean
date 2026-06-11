/-
  Cred Foundation Consequence

  Semantic consequence for the first-order foundation language.  This is the
  proof-theoretic target above structures, before adding a calculus.
-/

import Cred.Foundation.Laws

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

def ThresholdConsequence (t : Credence)
    (premises : List (Formula Func Pred)) (conclusion : Formula Func Pred) :
    Prop :=
  ∀ (M : Structure.{u, v, w} Func Pred) (env : M.Assignment),
    (∀ p ∈ premises, t ≤ M.evalFormula env p) →
    t ≤ M.evalFormula env conclusion

def CertaintyConsequence
    (premises : List (Formula Func Pred)) (conclusion : Formula Func Pred) :
    Prop :=
  ∀ (M : Structure.{u, v, w} Func Pred) (env : M.Assignment),
    (∀ p ∈ premises, M.evalFormula env p = 1) →
    M.evalFormula env conclusion = 1

theorem threshold_reflexivity (t : Credence) (φ : Formula Func Pred) :
    ThresholdConsequence.{u, v, w} t [φ] φ := by
  intro M env hprem
  exact hprem φ (List.mem_cons_self φ [])

theorem threshold_monotonicity (t : Credence)
    {Γ Δ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : ThresholdConsequence.{u, v, w} t Γ φ)
    (hsub : ∀ p ∈ Γ, p ∈ Δ) :
    ThresholdConsequence.{u, v, w} t Δ φ := by
  intro M env hprem
  exact h M env (fun p hp => hprem p (hsub p hp))

theorem threshold_cut (t : Credence)
    {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred}
    (h1 : ThresholdConsequence.{u, v, w} t Γ φ)
    (h2 : ThresholdConsequence.{u, v, w} t (φ :: Γ) ψ) :
    ThresholdConsequence.{u, v, w} t Γ ψ := by
  intro M env hprem
  have hφ := h1 M env hprem
  exact h2 M env (fun p hp => by
    cases List.mem_cons.mp hp with
    | inl h =>
        subst h
        exact hφ
    | inr h => exact hprem p h)

theorem certainty_reflexivity (φ : Formula Func Pred) :
    CertaintyConsequence.{u, v, w} [φ] φ := by
  intro M env hprem
  exact hprem φ (List.mem_cons_self φ [])

end Structure

end Foundation
end Cred
