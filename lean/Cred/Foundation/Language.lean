/-
  Cred Foundation Language

  This module starts the object language needed for a foundation layer.  It
  contains terms, equality, predicates, quantifiers, and the existing De Morgan
  connectives.  There is no object-language conditional constructor.
-/

namespace Cred
namespace Foundation

universe u v

inductive Term (Func : Type u) where
  | var : Nat → Term Func
  | app : Func → List (Term Func) → Term Func
deriving Repr

namespace Term

variable {Func : Type u}

mutual

def decEq [DecidableEq Func] :
    (a b : Term Func) → Decidable (a = b)
  | var m, var n =>
      if h : m = n then
        isTrue (by cases h; rfl)
      else
        isFalse (by
          intro hEq
          cases hEq
          exact h rfl)
  | app f args, app g args' =>
      if hf : f = g then
        match decEqList args args' with
        | isTrue hargs =>
            isTrue (by cases hf; cases hargs; rfl)
        | isFalse hargs =>
            isFalse (by
              intro hEq
              cases hEq
              exact hargs rfl)
      else
        isFalse (by
          intro hEq
          cases hEq
          exact hf rfl)
  | var _, app _ _ =>
      isFalse (by intro hEq; cases hEq)
  | app _ _, var _ =>
      isFalse (by intro hEq; cases hEq)

def decEqList [DecidableEq Func] :
    (args args' : List (Term Func)) → Decidable (args = args')
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro hEq; cases hEq)
  | _ :: _, [] => isFalse (by intro hEq; cases hEq)
  | t :: ts, u :: us =>
      match decEq t u with
      | isTrue ht =>
          match decEqList ts us with
          | isTrue hts =>
              isTrue (by cases ht; cases hts; rfl)
          | isFalse hts =>
              isFalse (by
                intro hEq
                cases hEq
                exact hts rfl)
      | isFalse ht =>
          isFalse (by
            intro hEq
            cases hEq
            exact ht rfl)

end

instance [DecidableEq Func] : DecidableEq (Term Func) :=
  decEq

def upRenaming (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

mutual

def rename (ρ : Nat → Nat) : Term Func → Term Func
  | var n => var (ρ n)
  | app f args => app f (renameList ρ args)

def renameList (ρ : Nat → Nat) : List (Term Func) → List (Term Func)
  | [] => []
  | t :: ts => rename ρ t :: renameList ρ ts

end

mutual

def subst (σ : Nat → Term Func) : Term Func → Term Func
  | var n => σ n
  | app f args => app f (substList σ args)

def substList (σ : Nat → Term Func) : List (Term Func) → List (Term Func)
  | [] => []
  | t :: ts => subst σ t :: substList σ ts

end

def liftSubst (σ : Nat → Term Func) : Nat → Term Func
  | 0 => var 0
  | n + 1 => rename Nat.succ (σ n)

def instSubst (τ : Term Func) : Nat → Term Func
  | 0 => τ
  | n + 1 => var n

end Term

inductive Formula (Func : Type u) (Pred : Type v) where
  | top : Formula Func Pred
  | bot : Formula Func Pred
  | atom : Pred → List (Term Func) → Formula Func Pred
  | equal : Term Func → Term Func → Formula Func Pred
  | neg : Formula Func Pred → Formula Func Pred
  | conj : Formula Func Pred → Formula Func Pred → Formula Func Pred
  | disj : Formula Func Pred → Formula Func Pred → Formula Func Pred
  | forallE : Formula Func Pred → Formula Func Pred
  | existsE : Formula Func Pred → Formula Func Pred
deriving Repr, DecidableEq

namespace Formula

variable {Func : Type u} {Pred : Type v}

def rename (ρ : Nat → Nat) : Formula Func Pred → Formula Func Pred
  | top => top
  | bot => bot
  | atom p args => atom p (Term.renameList ρ args)
  | equal lhs rhs => equal (Term.rename ρ lhs) (Term.rename ρ rhs)
  | neg φ => neg (φ.rename ρ)
  | conj φ ψ => conj (φ.rename ρ) (ψ.rename ρ)
  | disj φ ψ => disj (φ.rename ρ) (ψ.rename ρ)
  | forallE φ => forallE (φ.rename (Term.upRenaming ρ))
  | existsE φ => existsE (φ.rename (Term.upRenaming ρ))

def subst (σ : Nat → Term Func) : Formula Func Pred → Formula Func Pred
  | top => top
  | bot => bot
  | atom p args => atom p (Term.substList σ args)
  | equal lhs rhs => equal (Term.subst σ lhs) (Term.subst σ rhs)
  | neg φ => neg (φ.subst σ)
  | conj φ ψ => conj (φ.subst σ) (ψ.subst σ)
  | disj φ ψ => disj (φ.subst σ) (ψ.subst σ)
  | forallE φ => forallE (φ.subst (Term.liftSubst σ))
  | existsE φ => existsE (φ.subst (Term.liftSubst σ))

def instantiate (τ : Term Func) (φ : Formula Func Pred) : Formula Func Pred :=
  φ.subst (Term.instSubst τ)

def hasEquality : Formula Func Pred → Bool
  | top => false
  | bot => false
  | atom _ _ => false
  | equal _ _ => true
  | neg φ => φ.hasEquality
  | conj φ ψ => φ.hasEquality || ψ.hasEquality
  | disj φ ψ => φ.hasEquality || ψ.hasEquality
  | forallE φ => φ.hasEquality
  | existsE φ => φ.hasEquality

def hasQuantifier : Formula Func Pred → Bool
  | top => false
  | bot => false
  | atom _ _ => false
  | equal _ _ => false
  | neg φ => φ.hasQuantifier
  | conj φ ψ => φ.hasQuantifier || ψ.hasQuantifier
  | disj φ ψ => φ.hasQuantifier || ψ.hasQuantifier
  | forallE _ => true
  | existsE _ => true

end Formula

end Foundation
end Cred
