/-
  Cred Meta-Bootstrap: minimality is relative to the substrate.

  Issue #580. A minimal explicit seed is minimal only relative to a substrate.
  Shrinking the seed can move commitment into the substrate, decoder, transition,
  validator, or selector; it does not remove it. The conservation theorem makes
  this exact: relocating a substrate parameter into the seed/state leaves the run
  unchanged, so what is conserved is the pair (substrate, seed), not the size of
  the explicit seed alone. This is the companion to the fixed-substrate coherence
  of `Cred.sequential_eq_batch`: coherence assumes the substrate fixed; this asks
  what was already committed in the substrate before the run starts.
-/

import Cred.SeededSystem

namespace Cred

/-- The substrate-folded transition on `B × S`: carry the substrate `b` in the
    state and evolve `s` by `T b`. -/
def withSubstrate {B S : Type} (T : B → S → S) : B × S → B × S :=
  fun p => (p.1, T p.1 p.2)

/-- Commitment conservation: relocating the substrate `b` from a transition
    parameter into the seed/state leaves the run on `S` unchanged. The substrate
    is conserved, not removed, by shrinking the explicit seed. -/
theorem commitment_conservation {B S : Type} (T : B → S → S) (b : B) (s : S) :
    ∀ n, (withSubstrate T)^[n] (b, s) = (b, (T b)^[n] s) := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl

/-- The observable state orbit is identical whether the substrate is held as a
    transition parameter or folded into the seed. No presentation removes the
    commitment `b`; it only moves between substrate and seed. -/
theorem run_invariant_under_relocation {B S : Type} (T : B → S → S) (b : B) (s : S)
    (n : ℕ) : ((withSubstrate T)^[n] (b, s)).2 = (T b)^[n] s := by
  rw [commitment_conservation T b s n]

end Cred
