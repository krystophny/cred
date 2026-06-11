/-
  Cred Foundation Proof

  A small threshold calculus for first-order foundation formulas.  This is the
  first proof layer above `Foundation.Consequence`.
-/

import Cred.Foundation.Consequence

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

private theorem conj_le_left (a b : Credence) : a ⊗ b ≤ a := by
  change a.val * b.val ≤ a.val
  calc
    a.val * b.val ≤ a.val * 1 := by
      exact mul_le_mul_of_nonneg_left b.le_one a.nonneg
    _ = a.val := by ring

private theorem conj_le_right (a b : Credence) : a ⊗ b ≤ b := by
  rw [Credence.conj_comm]
  exact conj_le_left b a

private theorem le_disj_left (a b : Credence) : a ≤ a ⊔ b := by
  change a.val ≤ (a ⊔ b).val
  rw [Credence.disj_val]
  have h : 0 ≤ b.val * (1 - a.val) :=
    mul_nonneg b.nonneg (by linarith [a.le_one])
  linarith

private theorem le_disj_right (a b : Credence) : b ≤ a ⊔ b := by
  rw [Credence.disj_comm]
  exact le_disj_left b a

inductive Derivation (t : Credence) :
    List (Formula Func Pred) → Formula Func Pred → Prop where
  | hyp {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      φ ∈ Γ → Derivation t Γ φ
  | weaken {Γ Δ : List (Formula Func Pred)} {φ : Formula Func Pred} :
      Derivation t Γ φ →
      (∀ p ∈ Γ, p ∈ Δ) →
      Derivation t Δ φ
  | cut {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Derivation t Γ φ →
      Derivation t (φ :: Γ) ψ →
      Derivation t Γ ψ
  | conjElimLeft {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Derivation t Γ (.conj φ ψ) →
      Derivation t Γ φ
  | conjElimRight {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Derivation t Γ (.conj φ ψ) →
      Derivation t Γ ψ
  | disjIntroLeft {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Derivation t Γ φ →
      Derivation t Γ (.disj φ ψ)
  | disjIntroRight {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred} :
      Derivation t Γ ψ →
      Derivation t Γ (.disj φ ψ)

theorem derivation_sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : Derivation t Γ φ) :
    ThresholdConsequence.{u, v, w} t Γ φ := by
  induction h with
  | hyp hp =>
      intro M env hΓ
      exact hΓ _ hp
  | weaken h hsub ih =>
      intro M env hΔ
      exact ih M env (fun p hp => hΔ p (hsub p hp))
  | cut hφ hψ ihφ ihψ =>
      exact threshold_cut t ihφ ihψ
  | conjElimLeft h ih =>
      intro M env hΓ
      exact le_trans (ih M env hΓ) (conj_le_left _ _)
  | conjElimRight h ih =>
      intro M env hΓ
      exact le_trans (ih M env hΓ) (conj_le_right _ _)
  | disjIntroLeft h ih =>
      intro M env hΓ
      exact le_trans (ih M env hΓ) (le_disj_left _ _)
  | disjIntroRight h ih =>
      intro M env hΓ
      exact le_trans (ih M env hΓ) (le_disj_right _ _)

end Structure

end Foundation
end Cred
