/-
  Cred Foundation Calculus

  The foundation calculus combines the base threshold rules with crisp equality
  and quantifier rules. Its soundness assumes both law interfaces.
-/

import Cred.Foundation.Quantifier

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

def FoundationThresholdConsequence (t : Credence)
    (premises : List (Formula Func Pred)) (conclusion : Formula Func Pred) :
    Prop :=
  ∀ (M : Structure.{u, v, w} Func Pred) (env : M.Assignment),
    M.CrispEquality →
    M.QuantifierLaws →
    (∀ p ∈ premises, t ≤ M.evalFormula env p) →
    t ≤ M.evalFormula env conclusion

theorem threshold_to_foundation (t : Credence)
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : ThresholdConsequence.{u, v, w} t Γ φ) :
    FoundationThresholdConsequence.{u, v, w} t Γ φ := by
  intro M env _ _ hΓ
  exact h M env hΓ

theorem crisp_to_foundation (t : Credence)
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : CrispThresholdConsequence.{u, v, w} t Γ φ) :
    FoundationThresholdConsequence.{u, v, w} t Γ φ := by
  intro M env hEq _ hΓ
  exact h M env hEq hΓ

theorem quantifier_to_foundation (t : Credence)
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : QuantifierThresholdConsequence.{u, v, w} t Γ φ) :
    FoundationThresholdConsequence.{u, v, w} t Γ φ := by
  intro M env _ hQ hΓ
  exact h M env hQ hΓ

inductive FoundationDerivation (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Prop where
  | base {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      Derivation t Γ φ → FoundationDerivation t Γ φ
  | weaken {Γ Δ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      FoundationDerivation t Γ φ →
      (∀ p ∈ Γ, p ∈ Δ) →
      FoundationDerivation t Δ φ
  | cut {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      FoundationDerivation t Γ φ →
      FoundationDerivation t (φ :: Γ) ψ →
      FoundationDerivation t Γ ψ
  | equalityRefl {Γ : List (Formula Func Pred)} (τ : Term Func) :
      FoundationDerivation t Γ (.equal τ τ)
  | equalitySymm {Γ : List (Formula Func Pred)} {τ υ : Term Func} :
      FoundationDerivation t Γ (.equal τ υ) →
      FoundationDerivation t Γ (.equal υ τ)
  | equalityTrans {Γ : List (Formula Func Pred)} {τ υ χ : Term Func} :
      FoundationDerivation t Γ (.equal τ υ) →
      FoundationDerivation t Γ (.equal υ χ) →
      FoundationDerivation t Γ (.equal τ χ)
  | equalitySubst {Γ : List (Formula Func Pred)} {τ υ : Term Func}
      {φ : Formula Func Pred} :
      FoundationDerivation t Γ (.equal τ υ) →
      FoundationDerivation t Γ (Formula.instantiate τ φ) →
      FoundationDerivation t Γ (Formula.instantiate υ φ)
  | forallElim {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
      {τ : Term Func} :
      FoundationDerivation t Γ (.forallE φ) →
      FoundationDerivation t Γ (Formula.instantiate τ φ)
  | existsIntro {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
      {τ : Term Func} :
      FoundationDerivation t Γ (Formula.instantiate τ φ) →
      FoundationDerivation t Γ (.existsE φ)

theorem foundation_derivation_sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : FoundationDerivation t Γ φ) :
    FoundationThresholdConsequence.{u, v, w} t Γ φ := by
  induction h with
  | base h =>
      exact threshold_to_foundation t (derivation_sound h)
  | weaken h hsub ih =>
      intro M env hEq hQ hΔ
      exact ih M env hEq hQ (fun p hp => hΔ p (hsub p hp))
  | cut hφ hψ ihφ ihψ =>
      intro M env hEq hQ hΓ
      have hφVal := ihφ M env hEq hQ hΓ
      exact ihψ M env hEq hQ (fun p hp => by
        cases List.mem_cons.mp hp with
        | inl h =>
            subst h
            exact hφVal
        | inr h => exact hΓ p h)
  | equalityRefl τ =>
      exact crisp_to_foundation t (crisp_derivation_sound
        (CrispDerivation.equalityRefl τ))
  | equalitySymm h ih =>
      intro M env hEq hQ hΓ
      exact equality_symmetry_threshold t _ _ M env hEq (fun p hp => by
        cases List.mem_cons.mp hp with
        | inl hp =>
            subst hp
            exact ih M env hEq hQ hΓ
        | inr hp => cases hp)
  | equalityTrans h1 h2 ih1 ih2 =>
      intro M env hEq hQ hΓ
      exact equality_transitivity_threshold t _ _ _ M env hEq (fun p hp => by
        cases List.mem_cons.mp hp with
        | inl hp =>
            subst hp
            exact ih1 M env hEq hQ hΓ
        | inr hp =>
            cases List.mem_cons.mp hp with
            | inl hp =>
                subst hp
                exact ih2 M env hEq hQ hΓ
            | inr hp => cases hp)
  | equalitySubst hEqProof hφProof ihEq ihφ =>
      intro M env hEq hQ hΓ
      exact equality_substitution_threshold t _ _ _ M env hEq (fun p hp => by
        cases List.mem_cons.mp hp with
        | inl hp =>
            subst hp
            exact ihEq M env hEq hQ hΓ
        | inr hp =>
            cases List.mem_cons.mp hp with
            | inl hp =>
                subst hp
                exact ihφ M env hEq hQ hΓ
            | inr hp => cases hp)
  | forallElim h ih =>
      intro M env hEq hQ hΓ
      rw [evalFormula_instantiate]
      exact forall_elim_semantic t M env hQ _ _ (ih M env hEq hQ hΓ)
  | existsIntro h ih =>
      intro M env hEq hQ hΓ
      apply exists_intro_semantic t M env hQ _ _
      rw [← evalFormula_instantiate]
      exact ih M env hEq hQ hΓ

end Structure

end Foundation
end Cred
