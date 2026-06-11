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

end Structure

end Foundation
end Cred
