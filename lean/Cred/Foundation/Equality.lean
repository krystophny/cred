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

theorem equality_symmetry_threshold (t : Credence)
    (τ υ : Term Func) :
    CrispThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred τ υ] (Formula.equal υ τ) := by
  intro M env hEq hΓ
  by_cases h : M.evalTerm env τ = M.evalTerm env υ
  · change t ≤ M.eq (M.evalTerm env υ) (M.evalTerm env τ)
    rw [← h]
    simp [hEq.eq_refl, Credence.le_one']
  · have hzero : M.evalFormula env (.equal τ υ) = 0 := by
      simp [evalFormula, hEq.eq_zero_of_ne h]
    have hprem := hΓ (Formula.equal τ υ)
      (List.mem_cons_self (Formula.equal τ υ) [])
    rw [hzero] at hprem
    exact le_trans hprem (Credence.zero_le _)

theorem equality_transitivity_threshold (t : Credence)
    (τ υ χ : Term Func) :
    CrispThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred τ υ, Formula.equal υ χ]
      (Formula.equal τ χ) := by
  intro M env hEq hΓ
  by_cases hac : M.evalTerm env τ = M.evalTerm env χ
  · change t ≤ M.eq (M.evalTerm env τ) (M.evalTerm env χ)
    rw [hac]
    simp [hEq.eq_refl, Credence.le_one']
  · by_cases hab : M.evalTerm env τ = M.evalTerm env υ
    · by_cases hbc : M.evalTerm env υ = M.evalTerm env χ
      · exact False.elim (hac (hab.trans hbc))
      · have hzero : M.evalFormula env (.equal υ χ) = 0 := by
          simp [evalFormula, hEq.eq_zero_of_ne hbc]
        have hprem := hΓ (Formula.equal υ χ)
          (List.mem_cons_of_mem (Formula.equal τ υ)
            (List.mem_cons_self (Formula.equal υ χ) []))
        rw [hzero] at hprem
        exact le_trans hprem (Credence.zero_le _)
    · have hzero : M.evalFormula env (.equal τ υ) = 0 := by
        simp [evalFormula, hEq.eq_zero_of_ne hab]
      have hprem := hΓ (Formula.equal τ υ)
        (List.mem_cons_self (Formula.equal τ υ) [Formula.equal υ χ])
      rw [hzero] at hprem
      exact le_trans hprem (Credence.zero_le _)

theorem equality_substitution_threshold (t : Credence)
    (τ υ : Term Func) (φ : Formula Func Pred) :
    CrispThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred τ υ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) := by
  intro M env hEq hΓ
  by_cases h : M.evalTerm env τ = M.evalTerm env υ
  · have hφ := hΓ (Formula.instantiate τ φ)
      (List.mem_cons_of_mem (Formula.equal τ υ)
        (List.mem_cons_self (Formula.instantiate τ φ) []))
    rw [evalFormula_instantiate] at hφ
    rw [evalFormula_instantiate]
    rw [← h]
    exact hφ
  · have hzero : M.evalFormula env (.equal τ υ) = 0 := by
      simp [evalFormula, hEq.eq_zero_of_ne h]
    have hprem := hΓ (Formula.equal τ υ)
      (List.mem_cons_self (Formula.equal τ υ) [Formula.instantiate τ φ])
    rw [hzero] at hprem
    exact le_trans hprem (Credence.zero_le _)

inductive CrispDerivation (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Prop where
  | base {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      Derivation t Γ φ → CrispDerivation t Γ φ
  | equalityRefl {Γ : List (Formula Func Pred)} (τ : Term Func) :
      CrispDerivation t Γ (.equal τ τ)
  | equalitySymm {Γ : List (Formula Func Pred)} {τ υ : Term Func} :
      CrispDerivation t Γ (.equal τ υ) →
      CrispDerivation t Γ (.equal υ τ)
  | equalityTrans {Γ : List (Formula Func Pred)} {τ υ χ : Term Func} :
      CrispDerivation t Γ (.equal τ υ) →
      CrispDerivation t Γ (.equal υ χ) →
      CrispDerivation t Γ (.equal τ χ)

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
  | equalitySymm h ih =>
      intro M env hEq hΓ
      exact equality_symmetry_threshold t _ _ M env hEq (fun p hp => by
        cases List.mem_cons.mp hp with
        | inl hp =>
            subst hp
            exact ih M env hEq hΓ
        | inr hp => cases hp)
  | equalityTrans h1 h2 ih1 ih2 =>
      intro M env hEq hΓ
      exact equality_transitivity_threshold t _ _ _ M env hEq (fun p hp => by
        cases List.mem_cons.mp hp with
        | inl hp =>
            subst hp
            exact ih1 M env hEq hΓ
        | inr hp =>
            cases List.mem_cons.mp hp with
            | inl hp =>
                subst hp
                exact ih2 M env hEq hΓ
            | inr hp => cases hp)

end Structure

end Foundation
end Cred
