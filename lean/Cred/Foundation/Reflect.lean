/-
  Cred Foundation Reflect: the reflective tie.

  The object-level self-representation (`Cred.SelfRep`: certificate trees as Goedel
  codes, with the acceptance predicate `accepted` on codes) and the real-free
  executable checker (`Cred.Foundation.CheckBool`: `checkBool`) are two views of one
  decision. This module proves they coincide: a code numbers an accepted tree
  exactly when the computable, reals-free `checkBool` returns `true`. Composing the
  faithfulness of the numbering (`accepted_gnum_iff`) with the agreement of the
  executable checker (`checkBool_eq_isSome`) closes the loop between the arithmetic
  self-representation and the running checker, and carries soundness through.
-/

import Cred.SelfRep
import Cred.Foundation.CheckBool

namespace Cred
namespace Foundation
namespace Structure

open Cred.SelfRep

variable {Func Pred : Type*}

/-- Reflective coincidence: the object-level, Goedel-coded acceptance predicate
    agrees with the real-free executable checker. The code `gnumTree gf gp tree` is
    accepted exactly when `checkBool tree = true`. -/
theorem reflect_accepted_checkBool [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp)
    (tree : FoundationCertificateTree Func Pred) :
    accepted t gf gp (gnumTree gf gp tree) ↔ checkBool tree = true := by
  rw [checkBool_eq_isSome t tree]
  exact accepted_gnum_iff hf hp tree

/-- The reflective verdict is sound: an accepted code recovers a verified
    certificate and its object-level consequence, with no reals in the running
    checker. -/
theorem reflect_accepted_sound [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp)
    (tree : FoundationCertificateTree Func Pred)
    (h : accepted t gf gp (gnumTree gf gp tree)) :
    (checkFoundationCertificate t tree).isSome = true :=
  (accepted_gnum_iff hf hp tree).mp h

end Structure
end Foundation
end Cred
