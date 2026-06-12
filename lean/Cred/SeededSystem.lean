/-
  Cred Seeded Systems: the universal-bootstrapping skeleton.

  This is the formal core of the bootstrapping thesis. A bootstrap never starts
  from nothing: it needs a state space, an allowed seed, a transition rule, a
  validator, and a correctness relation. `SeededSystem` bundles exactly that,
  generalizing `Credence.CommitmentSystem` from one metric orbit to an abstract
  state space.

  Scope (guardrail): only the formal schema lives here. The compiler, proof-kernel,
  AI-assisted-design, and biological-origin readings are structured analogies and
  belong in prose, not in this file.

  Key facts:
  - no_empty_bootstrap: with no seed there is nothing to start from.
  - SelfHosts s := E s (T s): the state reproduces itself, `compile(b) ≃ b`.
  - selfHosts_of_fixed: an E-fixed point of the transition self-hosts.
  - the commitment system embeds, with its fixed point and degenerate element
    as self-hosting states.
-/

import Cred.Commitment

namespace Cred

/-- A seeded transition system: the abstract skeleton of a bootstrap. `T` folds
    the substrate into the transition, `V` validates a step, `E` is the
    correctness/equivalence relation, and `Seed` marks allowed seeds. -/
structure SeededSystem where
  /-- The state/artifact space. -/
  S : Type
  /-- The allowed seeds. -/
  Seed : S → Prop
  /-- The transition / build / update operator (substrate folded in). -/
  T : S → S
  /-- The validator on a step `(previous, next)`. -/
  V : S → S → Prop
  /-- The correctness / observational-equivalence relation. -/
  E : S → S → Prop

namespace SeededSystem

variable (M : SeededSystem)

/-- The bootstrap orbit: `n` transition steps from a seed. -/
def run (s0 : M.S) (n : ℕ) : M.S := M.T^[n] s0

@[simp] theorem run_zero (s0 : M.S) : M.run s0 0 = s0 := rfl

@[simp] theorem run_succ (s0 : M.S) (n : ℕ) :
    M.run s0 (n + 1) = M.T (M.run s0 n) :=
  Function.iterate_succ_apply' M.T n s0

/-- A state self-hosts when the transition reproduces it up to `E`: `E s (T s)`,
    the compiler that recompiles to itself. -/
def SelfHosts (s : M.S) : Prop := M.E s (M.T s)

/-- No empty bootstrap: with no seed there is nothing to start a run from. The
    missing information has moved into the substrate, not vanished. -/
theorem no_empty_bootstrap (h : ¬ ∃ s, M.Seed s) : ∀ s, ¬ M.Seed s := by
  intro s hs; exact h ⟨s, hs⟩

/-- An `E`-fixed point of the transition self-hosts. -/
theorem selfHosts_of_fixed {s : M.S} (hE : M.E s s) (hfix : M.T s = s) :
    M.SelfHosts s := by
  show M.E s (M.T s)
  rw [hfix]; exact hE

/-- A transition fixed point is stationary: every run from it stays put. -/
theorem run_const_of_fixed {s : M.S} (hfix : M.T s = s) :
    ∀ n, M.run s n = s := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => rw [run_succ, ih]; exact hfix

end SeededSystem

/-! ## The commitment system is a seeded system

The abstract irreducible-commitment structure is the metric instance of the
bootstrap schema: the refinement operator is the transition, equality is
correctness, and both the fixed point and the degenerate element self-host. -/

/-- Every commitment system is a seeded system. -/
noncomputable def Credence.CommitmentSystem.toSeeded
    (C : Credence.CommitmentSystem) : SeededSystem where
  S := Credence
  Seed := fun _ => True
  T := C.op
  V := fun _ _ => True
  E := Eq

/-- The fixed point self-hosts: it is reproduced exactly by the transition. -/
theorem Credence.CommitmentSystem.fp_selfHosts (C : Credence.CommitmentSystem) :
    C.toSeeded.SelfHosts C.fp := by
  apply SeededSystem.selfHosts_of_fixed
  · rfl
  · exact C.fixedPoint

/-- The degenerate element self-hosts too: it is an absorbing fixed point. -/
theorem Credence.CommitmentSystem.deg_selfHosts (C : Credence.CommitmentSystem) :
    C.toSeeded.SelfHosts C.deg := by
  apply SeededSystem.selfHosts_of_fixed
  · rfl
  · exact C.degAbsorbing

/-! ## A minimal self-hosting instance

The schema is inhabited by a genuine self-hosting fixed point: a one-state system
whose transition is the identity, so its state recompiles to itself. -/

/-- Minimal compiler-flavoured instance: one state, identity transition, equality
    as correctness. The state self-hosts (`compile(b) ≃ b`). -/
def trivialSelfHost : SeededSystem where
  S := Unit
  Seed := fun _ => True
  T := id
  V := fun _ _ => True
  E := Eq

theorem trivialSelfHost_selfHosts (u : Unit) : trivialSelfHost.SelfHosts u := rfl

end Cred
