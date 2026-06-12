/-
  Cred Approx Example: Variational Integrator / Discrete Action (issue #620)

  A variational integrator is built from a discrete Lagrangian rather than from
  a truncated Taylor expansion. For the free particle (quadratic kinetic
  Lagrangian) the discrete Lagrangian over one step is

      Ld a b h = (b - a)^2 / (2 h),

  the kinetic energy of the discrete velocity `(b - a) / h`. Stationarity of the
  two-step discrete action `S = Ld q0 q1 h + Ld q1 q2 h` in the interior node
  `q1` is the discrete Euler-Lagrange (DEL) equation

      D2 Ld q0 q1 + D1 Ld q1 q2 = 0,

  which for this `Ld` reads `(q1 - q0)/h - (q2 - q1)/h = 0`, i.e.
  `q2 - 2 q1 + q0 = 0`: the free-particle leapfrog update.

  The structure preserved is not pointwise accuracy but discrete momentum
  `p = (q1 - q0)/h`. We score a stencil crisply by DEL and show:

  * the discrete momentum is conserved on any DEL stencil (the discrete Noether
    statement for the free particle);
  * the explicit leapfrog update `q2 = 2 q1 - q0` produces a DEL stencil, so it
    is exactly the variational update;
  * the stencil-shift self-map keeps the DEL structure exactly (`Preserves`);
  * a biased update `q2 = 2 q1 - q0 + b` breaks DEL whenever `b ≠ 0`, giving a
    concrete momentum-leak counterexample and a non-preserving scheme.
-/

import Cred.Approx.Structure
import Mathlib.Tactic

namespace Cred

namespace Approx

open Credence

/-! ## Discrete Lagrangian and Euler-Lagrange residual for the free particle -/

/-- Discrete Lagrangian of the free particle over one step of size `h`:
    the kinetic energy `(velocity)^2 / 2` of the discrete velocity `(b - a)/h`. -/
noncomputable def Ld (a b h : ℝ) : ℝ := (b - a) ^ 2 / (2 * h)

/-- Discrete momentum carried across the step from `a` to `b`: `(b - a)/h`. -/
noncomputable def discMom (a b h : ℝ) : ℝ := (b - a) / h

/-- The discrete Euler-Lagrange equation for the free-particle three-point
    stencil `(q0, q1, q2)`: `q2 - 2 q1 + q0 = 0`. This is the stationarity
    condition of `Ld q0 q1 h + Ld q1 q2 h` in the interior node `q1`. -/
def DEL (q0 q1 q2 : ℝ) : Prop := q2 - 2 * q1 + q0 = 0

-- `DEL` is a real equality, so its decidability is classical (noncomputable).
noncomputable instance : DecidablePred (fun p : ℝ × ℝ × ℝ => DEL p.1 p.2.1 p.2.2) :=
  fun _ => Classical.dec _

/-- DEL membership of a stencil as a 0/1 credence structure. -/
noncomputable def delScore : ℝ × ℝ × ℝ → Credence :=
  crispScore (fun p => DEL p.1 p.2.1 p.2.2)

@[simp] theorem delScore_one_iff (p : ℝ × ℝ × ℝ) :
    delScore p = 1 ↔ DEL p.1 p.2.1 p.2.2 :=
  crispScore_one_iff _ p

/-! ## The discrete momentum is conserved on every DEL stencil (Noether) -/

/-- Discrete Noether for the free particle: a DEL stencil carries the same
    discrete momentum on its incoming and outgoing legs. This holds for every
    nonzero step `h`; it is the structural invariant the variational origin
    guarantees, beyond any pointwise accuracy estimate. -/
theorem del_momentum_conserved (q0 q1 q2 h : ℝ) (hh : h ≠ 0)
    (hdel : DEL q0 q1 q2) : discMom q1 q2 h = discMom q0 q1 h := by
  unfold discMom DEL at *
  rw [div_eq_div_iff hh hh]
  linear_combination h * hdel

/-- Equivalently, on a DEL stencil the two-step second difference vanishes,
    so the discrete momentum increment is zero. -/
theorem del_momentum_increment_zero (q0 q1 q2 h : ℝ) (hh : h ≠ 0)
    (hdel : DEL q0 q1 q2) : discMom q1 q2 h - discMom q0 q1 h = 0 := by
  rw [del_momentum_conserved q0 q1 q2 h hh hdel]; ring

/-! ## The explicit leapfrog update is the variational update -/

/-- The explicit free-particle leapfrog map: from the two latest nodes `q0, q1`
    it produces the next node `2 q1 - q0`. -/
def leapfrog (q0 q1 : ℝ) : ℝ := 2 * q1 - q0

/-- The leapfrog update closes a DEL stencil exactly: `(q0, q1, leapfrog q0 q1)`
    satisfies the discrete Euler-Lagrange equation, so leapfrog *is* the
    variational integrator for the free particle. -/
theorem leapfrog_is_DEL (q0 q1 : ℝ) : DEL q0 q1 (leapfrog q0 q1) := by
  unfold DEL leapfrog; ring

/-- Hence the leapfrog stencil conserves discrete momentum for every nonzero
    step: variational origin gives a conserved quantity for free. -/
theorem leapfrog_momentum_conserved (q0 q1 h : ℝ) (hh : h ≠ 0) :
    discMom q1 (leapfrog q0 q1) h = discMom q0 q1 h :=
  del_momentum_conserved q0 q1 (leapfrog q0 q1) h hh (leapfrog_is_DEL q0 q1)

/-! ## The variational shift map preserves the DEL structure -/

/-- The stencil-advance self-map: drop the oldest node and append the leapfrog
    successor, `(q0, q1, q2) ↦ (q1, q2, 2 q2 - q1)`. This is one variational
    step on the moving three-point window. -/
def variationalStep (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (p.2.1, p.2.2, leapfrog p.2.1 p.2.2)

/-- Advancing the window always lands on a DEL stencil, regardless of where it
    started: the new triple's interior balance is the leapfrog identity. Hence
    `variationalStep` preserves the DEL structure exactly. -/
theorem variationalStep_preserves : Preserves delScore variationalStep := by
  intro p _
  rw [ExactPreserves_def, delScore_one_iff]
  exact leapfrog_is_DEL p.2.1 p.2.2

/-! ## A perturbed update leaks momentum -/

/-- A perturbed position update that adds a fixed bias `b` to the leapfrog
    successor: `q2 = 2 q1 - q0 + b`. For `b ≠ 0` it leaves the variational
    manifold. -/
def biasedStep (b q0 q1 : ℝ) : ℝ := 2 * q1 - q0 + b

/-- The biased update violates DEL exactly when the bias is nonzero. -/
theorem biasedStep_DEL_iff (b q0 q1 : ℝ) :
    DEL q0 q1 (biasedStep b q0 q1) ↔ b = 0 := by
  unfold DEL biasedStep
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- Concrete momentum leak: with bias `b = 1`, step `h = 1`, and nodes
    `q0 = 0, q1 = 0`, the biased successor is `1`, the stencil fails DEL, and
    the outgoing discrete momentum `1` differs from the incoming `0`. -/
theorem biasedStep_breaks_momentum :
    ¬ DEL 0 0 (biasedStep 1 0 0) ∧
      discMom (0 : ℝ) (biasedStep 1 0 0) 1 ≠ discMom (0 : ℝ) 0 1 := by
  refine ⟨?_, ?_⟩
  · rw [biasedStep_DEL_iff]; norm_num
  · unfold discMom biasedStep; norm_num

/-- The biased shift map (bias `1`) is not a DEL-preservation scheme: starting
    from a genuine DEL stencil, its image fails DEL. -/
theorem biasedStep_not_preserves :
    ¬ Preserves delScore (fun p : ℝ × ℝ × ℝ => (p.2.1, p.2.2, biasedStep 1 p.2.1 p.2.2)) := by
  intro hpres
  -- Start from the trivial DEL stencil `(0, 0, 0)`.
  have hstart : ExactPreserves delScore (0, 0, 0) := by
    rw [ExactPreserves_def, delScore_one_iff]
    show DEL 0 0 0
    unfold DEL; norm_num
  have himg := hpres (0, 0, 0) hstart
  rw [ExactPreserves_def, delScore_one_iff] at himg
  -- `himg` claims the biased image stencil satisfies DEL, contradicting the bias.
  have himg' : DEL 0 0 (biasedStep 1 0 0) := himg
  rw [biasedStep_DEL_iff] at himg'
  norm_num at himg'

end Approx

end Cred
