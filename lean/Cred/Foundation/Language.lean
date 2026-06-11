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
deriving Repr

namespace Formula

variable {Func : Type u} {Pred : Type v}

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
