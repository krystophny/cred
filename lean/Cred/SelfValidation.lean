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

/-- Non-crisp self-validation is consistent: at any point there is a faithful
    self-certification, one that reports its own value, and it equals `half`. The
    constant `half` is faithful by the liar fixed point `~half = half`. So a system
    can certify itself non-crisply, where a crisp self-certification is impossible. -/
theorem faithful_self_validation_exists {S : Type} (d : S) :
    ∃ cert : S → Credence, cert d = ~ (cert d) ∧ cert d = half :=
  ⟨fun _ => half, liar_fixed_point.symm, rfl⟩

/-- The ceiling on self-trust: any self-certification that is not `half` is
    unfaithful, it does not report its own value at the self-application point.
    Higher self-confidence than `half` is available only by giving up faithfulness;
    a system cannot faithfully certify itself with more than the interior value. -/
theorem self_validation_unfaithful_of_ne_half {S : Type} (cert : S → Credence)
    (d : S) (h : cert d ≠ half) : cert d ≠ ~ (cert d) :=
  fun hfix => h (self_validation_not_crisp cert d hfix)

end Cred
