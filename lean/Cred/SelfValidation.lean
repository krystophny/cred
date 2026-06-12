/-
  Cred Self-Validation: self-hosting is not self-justifying.

  The operational and meta levels of the seed/hierarchy problem look alike (both
  are fixed-point phenomena) but differ in kind. Operationally, a state can host
  itself: a transition fixed point reproduces it, E s (T s), and this is freely
  available (a compiler that compiles to itself). At the meta level, a system
  cannot crisply certify itself: a credence-valued certification that, at a
  self-application point, reports its own non-certification is pinned to the
  interior value half, so it gives no crisp verdict on itself. This is the
  Tarski-Goedel boundary in graded form, and it is why the reflection tower
  ascends rather than closing.
-/

import Cred.SeededSystem

namespace Cred

open Credence

/-- Operational self-hosting is available: some seeded system has a state the
    transition reproduces, `E s (T s)`. -/
theorem selfHosting_available : ∃ (M : SeededSystem) (s : M.S), M.SelfHosts s :=
  ⟨trivialSelfHost, (), trivialSelfHost_selfHosts ()⟩

/-- Meta self-validation is not crisp: a credence-valued certification that at a
    self-application point reports its own non-certification is pinned to `half`. -/
theorem self_validation_not_crisp {S : Type} (cert : S → Credence) (d : S)
    (hdiag : cert d = ~ (cert d)) : cert d = half :=
  neg_fixed_point_unique (cert d) hdiag.symm

/-- No crisp self-validation: the self-certifying value is neither impossibility
    nor certainty. A system that can host itself still cannot certify itself with
    a clean yes or no. -/
theorem no_crisp_self_validation {S : Type} (cert : S → Credence) (d : S)
    (hdiag : cert d = ~ (cert d)) : cert d ≠ 0 ∧ cert d ≠ 1 := by
  rw [self_validation_not_crisp cert d hdiag]
  refine ⟨?_, ?_⟩
  · intro h
    have hv : (half : Credence).val = (0 : Credence).val := congrArg Credence.val h
    rw [half_val, zero_val] at hv; norm_num at hv
  · intro h
    have hv : (half : Credence).val = (1 : Credence).val := congrArg Credence.val h
    rw [half_val, one_val] at hv; norm_num at hv

end Cred
