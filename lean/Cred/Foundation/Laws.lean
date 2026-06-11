/-
  Cred Foundation Laws

  The raw semantics keeps equality and quantifiers explicit.  This module names
  the laws a foundation layer may require from those operations.
-/

import Cred.Foundation.Semantics

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v} (M : Structure Func Pred)

structure CrispEquality : Prop where
  eq_refl : ∀ x : M.Domain, M.eq x x = 1
  eq_one_imp : ∀ {x y : M.Domain}, M.eq x y = 1 → x = y
  eq_zero_of_ne : ∀ {x y : M.Domain}, x ≠ y → M.eq x y = 0

structure QuantifierLaws : Prop where
  all_le_instance : ∀ (f : M.Domain → Credence) (x : M.Domain), M.all f ≤ f x
  instance_le_ex : ∀ (f : M.Domain → Credence) (x : M.Domain), f x ≤ M.ex f
  all_one : M.all (fun _ : M.Domain => 1) = 1
  ex_zero : M.ex (fun _ : M.Domain => 0) = 0

theorem equality_no_false_positive (h : M.CrispEquality)
    {x y : M.Domain} :
    M.eq x y = 1 → x = y :=
  h.eq_one_imp

theorem equality_reflexive_one (h : M.CrispEquality)
    (x : M.Domain) :
    M.eq x x = 1 :=
  h.eq_refl x

theorem forall_instantiates (h : M.QuantifierLaws)
    (f : M.Domain → Credence) (x : M.Domain) :
    M.all f ≤ f x :=
  h.all_le_instance f x

theorem exists_introduces (h : M.QuantifierLaws)
    (f : M.Domain → Credence) (x : M.Domain) :
    f x ≤ M.ex f :=
  h.instance_le_ex f x

end Structure

end Foundation
end Cred
