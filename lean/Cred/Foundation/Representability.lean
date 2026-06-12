/-
  Cred Foundation Representability.

  Issue #521/#525, the recursion-theoretic half of representability. Provability,
  the acceptance of a certificate, is a recursive predicate: it coincides with a
  total computable, real-free decision (`checkCode`). This is what the
  second-incompleteness boundary needs at the recursion-theoretic level. The
  deeper part, a PA-internal Sigma-1 arithmetic formula provable exactly when the
  predicate holds, is the classical arithmetization that mathlib does not yet
  provide and is recorded as remaining.
-/

import Cred.Foundation.CodeChecker

namespace Cred
namespace Foundation
namespace Structure

open Cred.SelfRep

variable {Func Pred : Type*}

/-- Provability is representable as a total computable decision: the acceptance of
    the code of a certificate tree coincides with the value of the computable,
    real-free `checkCode`. Provability is therefore a recursive predicate. -/
theorem provability_representable [DecidableEq Func] [DecidableEq Pred]
    {df : Nat → Option Func} {dp : Nat → Option Pred}
    {gf : Func → Nat} {gp : Pred → Nat}
    (hdf : ∀ f, df (gf f) = some f) (hdp : ∀ p, dp (gp p) = some p)
    (hgf : Function.Injective gf) (hgp : Function.Injective gp)
    (t : Credence) (fuel : Nat)
    (tree : FoundationCertificateTree Func Pred)
    (hfuel : treeSize tree ≤ fuel) :
    accepted t gf gp (gnumTree gf gp tree) ↔
      checkCode df dp fuel (gnumTree gf gp tree) = true :=
  checkCode_gnumTree_accepted hdf hdp hgf hgp t fuel tree hfuel

end Structure
end Foundation
end Cred
