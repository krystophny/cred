/-
  Cred Foundation Semantics

  This module interprets the first-order foundation language into credences.
  Equality and quantifiers are semantic operations of the structure; later
  modules can add crispness, extensionality, or completeness laws.
-/

import Cred.Foundation.Language
import Cred.Core.Value

namespace Cred
namespace Foundation

universe u v w

open Credence

structure Structure (Func : Type u) (Pred : Type v) where
  Domain : Type w
  witness : Domain
  func : Func → List Domain → Domain
  pred : Pred → List Domain → Credence
  eq : Domain → Domain → Credence
  all : (Domain → Credence) → Credence
  ex : (Domain → Credence) → Credence

namespace Structure

variable {Func : Type u} {Pred : Type v} (M : Structure Func Pred)

abbrev Assignment := Nat → M.Domain

def update (env : M.Assignment) (x : M.Domain) : M.Assignment
  | 0 => x
  | n + 1 => env n

mutual

def evalTerm (env : M.Assignment) : Term Func → M.Domain
  | .var n => env n
  | .app f args => M.func f (evalTermList env args)

def evalTermList (env : M.Assignment) : List (Term Func) → List M.Domain
  | [] => []
  | t :: ts => evalTerm env t :: evalTermList env ts

end

mutual

theorem evalTerm_rename (env : M.Assignment) (ρ : Nat → Nat) :
    ∀ t : Term Func,
      evalTerm M env (Term.rename ρ t) =
        evalTerm M (fun n => env (ρ n)) t
  | .var n => rfl
  | .app f args => by
      simp [Term.rename, evalTerm, evalTermList_rename env ρ args]

theorem evalTermList_rename (env : M.Assignment) (ρ : Nat → Nat) :
    ∀ ts : List (Term Func),
      evalTermList M env (Term.renameList ρ ts) =
        evalTermList M (fun n => env (ρ n)) ts
  | [] => rfl
  | t :: ts => by
      simp [Term.renameList, evalTermList, evalTerm_rename env ρ t,
        evalTermList_rename env ρ ts]

end

mutual

theorem evalTerm_subst (env : M.Assignment) (σ : Nat → Term Func) :
    ∀ t : Term Func,
      evalTerm M env (Term.subst σ t) =
        evalTerm M (fun n => evalTerm M env (σ n)) t
  | .var n => rfl
  | .app f args => by
      simp [Term.subst, evalTerm, evalTermList_subst env σ args]

theorem evalTermList_subst (env : M.Assignment) (σ : Nat → Term Func) :
    ∀ ts : List (Term Func),
      evalTermList M env (Term.substList σ ts) =
        evalTermList M (fun n => evalTerm M env (σ n)) ts
  | [] => rfl
  | t :: ts => by
      simp [Term.substList, evalTermList, evalTerm_subst env σ t,
        evalTermList_subst env σ ts]

end

theorem evalTerm_upRenaming_update (env : M.Assignment) (ρ : Nat → Nat)
    (x : M.Domain) (t : Term Func) :
    evalTerm M (update M env x) (Term.rename (Term.upRenaming ρ) t) =
      evalTerm M (update M (fun n => env (ρ n)) x) t := by
  rw [evalTerm_rename]
  congr
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem evalTerm_liftSubst_update (env : M.Assignment)
    (σ : Nat → Term Func) (x : M.Domain) :
    ∀ n : Nat,
      evalTerm M (update M env x) (Term.liftSubst σ n) =
        update M (fun k => evalTerm M env (σ k)) x n
  | 0 => rfl
  | n + 1 => by
      simp [Term.liftSubst]
      rw [evalTerm_rename]
      rfl

def evalFormula (env : M.Assignment) :
    Formula Func Pred → Credence
  | .top => 1
  | .bot => 0
  | .atom p args => M.pred p (evalTermList M env args)
  | .equal lhs rhs => M.eq (evalTerm M env lhs) (evalTerm M env rhs)
  | .neg φ => ~(evalFormula env φ)
  | .conj φ ψ => evalFormula env φ ⊗ evalFormula env ψ
  | .disj φ ψ => evalFormula env φ ⊔ evalFormula env ψ
  | .forallE φ => M.all (fun x => evalFormula (update M env x) φ)
  | .existsE φ => M.ex (fun x => evalFormula (update M env x) φ)

theorem evalFormula_rename (env : M.Assignment) (ρ : Nat → Nat) :
    ∀ φ : Formula Func Pred,
      evalFormula M env (Formula.rename ρ φ) =
        evalFormula M (fun n => env (ρ n)) φ
  | .top => rfl
  | .bot => rfl
  | .atom p args => by
      simp [Formula.rename, evalFormula, evalTermList_rename]
  | .equal lhs rhs => by
      simp [Formula.rename, evalFormula, evalTerm_rename]
  | .neg φ => by
      simp [Formula.rename, evalFormula, evalFormula_rename env ρ φ]
  | .conj φ ψ => by
      simp [Formula.rename, evalFormula, evalFormula_rename env ρ φ,
        evalFormula_rename env ρ ψ]
  | .disj φ ψ => by
      simp [Formula.rename, evalFormula, evalFormula_rename env ρ φ,
        evalFormula_rename env ρ ψ]
  | .forallE φ => by
      simp [Formula.rename, evalFormula]
      congr
      funext x
      rw [evalFormula_rename (update M env x) (Term.upRenaming ρ) φ]
      congr
      funext n
      cases n with
      | zero => rfl
      | succ n => rfl
  | .existsE φ => by
      simp [Formula.rename, evalFormula]
      congr
      funext x
      rw [evalFormula_rename (update M env x) (Term.upRenaming ρ) φ]
      congr
      funext n
      cases n with
      | zero => rfl
      | succ n => rfl

theorem evalFormula_subst (env : M.Assignment) (σ : Nat → Term Func) :
    ∀ φ : Formula Func Pred,
      evalFormula M env (Formula.subst σ φ) =
        evalFormula M (fun n => evalTerm M env (σ n)) φ
  | .top => rfl
  | .bot => rfl
  | .atom p args => by
      simp [Formula.subst, evalFormula, evalTermList_subst]
  | .equal lhs rhs => by
      simp [Formula.subst, evalFormula, evalTerm_subst]
  | .neg φ => by
      simp [Formula.subst, evalFormula, evalFormula_subst env σ φ]
  | .conj φ ψ => by
      simp [Formula.subst, evalFormula, evalFormula_subst env σ φ,
        evalFormula_subst env σ ψ]
  | .disj φ ψ => by
      simp [Formula.subst, evalFormula, evalFormula_subst env σ φ,
        evalFormula_subst env σ ψ]
  | .forallE φ => by
      simp [Formula.subst, evalFormula]
      congr
      funext x
      have hAssign : (fun n => evalTerm M (update M env x)
          (Term.liftSubst σ n)) =
          update M (fun n => evalTerm M env (σ n)) x := by
        funext n
        exact evalTerm_liftSubst_update M env σ x n
      rw [evalFormula_subst (update M env x) (Term.liftSubst σ) φ]
      congr
  | .existsE φ => by
      simp [Formula.subst, evalFormula]
      congr
      funext x
      have hAssign : (fun n => evalTerm M (update M env x)
          (Term.liftSubst σ n)) =
          update M (fun n => evalTerm M env (σ n)) x := by
        funext n
        exact evalTerm_liftSubst_update M env σ x n
      rw [evalFormula_subst (update M env x) (Term.liftSubst σ) φ]
      congr

end Structure

end Foundation
end Cred
