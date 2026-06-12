/-
  Cred Toy Model: Irreducible Commitment as an Iterated Map

  The minimal toy model of the irreducible-commitment principle: a credence is
  refined by iterating a map on the unit interval. Four properties, each a
  proven lemma, capture the principle:

  P1 (toyA_seed_matters): the finite orbit depends on the seed — locally the
     starting commitment is unavoidable and shapes the value.
  P2 (toyA_contraction_bound + toyA_contraction_tendsto): under the averaging
     contraction toward a target, the seed washes out — the distance to the
     target is bounded by (1/2)^n · |x0 - t| and tends to 0 from any seed.
     This is the prior-independence / merging-of-opinions analogue.
  P3 (toyA_absorbing_zero): under the product map g x = x ⊗ e, zero is
     absorbing, so a degenerate (impossible) seed never recovers. This is
     Cromwell's rule / no ex falso, the iterated face of conditioning_zero_any.
  P4 (toyA_target_fixed + toyA_limit_fixed): the limit the base level converges
     to satisfies the self-consistency equation f t = t — the meta level
     certifies the value the base level assumed.
-/

import Cred.Cond.Admissible
import Mathlib.Analysis.SpecificLimits.Basic

namespace Cred

namespace Credence

open Filter Topology

/-! ## The averaging contraction toward a target

`toyA t` sends `x` to the midpoint of `x` and the target `t`. It contracts
toward `t` with ratio `1/2`, so the orbit of any seed converges to `t`. -/

/-- One refinement step: average the current credence with the target `t`. -/
noncomputable def toyA (t x : Credence) : Credence where
  val := (x.val + t.val) / 2
  nonneg := by have := x.nonneg; have := t.nonneg; linarith
  le_one := by have := x.le_one; have := t.le_one; linarith

@[simp] theorem toyA_val (t x : Credence) : (toyA t x).val = (x.val + t.val) / 2 := rfl

/-- The signed distance to the target halves at each step. -/
theorem toyA_dist_step (t x : Credence) :
    (toyA t x).val - t.val = (x.val - t.val) / 2 := by
  simp only [toyA_val]; ring

/-! ### P4 (fixed point): the target is self-consistent -/

/-- The target is a genuine fixed point: `toyA t t = t`. The meta level
    certifies the value the base level converged to. -/
theorem toyA_target_fixed (t : Credence) : toyA t t = t := by
  ext; simp only [toyA_val]; ring

/-! ### P1 (seed matters locally): the orbit depends on the seed

With target `half`, the seeds `0` and `1` already diverge after one step. -/

/-- The finite orbit depends on the seed: distinct seeds give a distinct
    iterate at some step. Concretely, after one averaging step toward `half`,
    seed `0` lands at `1/4` and seed `1` at `3/4`. -/
theorem toyA_seed_matters :
    ∃ (x₀ x₀' : Credence) (n : ℕ),
      (toyA half)^[n] x₀ ≠ (toyA half)^[n] x₀' := by
  refine ⟨0, 1, 1, ?_⟩
  simp only [Function.iterate_one]
  intro h
  have hv : (toyA half 0).val = (toyA half 1).val := congrArg (·.val) h
  simp only [toyA_val, zero_val, one_val, half_val] at hv
  norm_num at hv

/-! ### P2 (seed washes out): geometric contraction to the target -/

/-- The iterate's signed distance to the target is `(1/2)^n · (x₀ - t)`. -/
theorem toyA_iterate_dist (t x₀ : Credence) (n : ℕ) :
    ((toyA t)^[n] x₀).val - t.val = (1 / 2) ^ n * (x₀.val - t.val) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', toyA_dist_step, ih, pow_succ]
    ring

/-- Explicit geometric bound: the distance to the target after `n` steps is
    `(1/2)^n · |x₀ - t|`, independent of which seed `x₀` we started from. -/
theorem toyA_contraction_bound (t x₀ : Credence) (n : ℕ) :
    |((toyA t)^[n] x₀).val - t.val| = (1 / 2) ^ n * |x₀.val - t.val| := by
  rw [toyA_iterate_dist, abs_mul, abs_pow]
  congr 1
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- The seed washes out: from any seed `x₀`, the iterate converges to the
    target `t`. Genuine `Tendsto` statement (merging of opinions). -/
theorem toyA_contraction_tendsto (t x₀ : Credence) :
    Tendsto (fun n => ((toyA t)^[n] x₀).val) atTop (𝓝 t.val) := by
  have hgeom : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * (x₀.val - t.val)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using h.mul_const (x₀.val - t.val)
  have hshift : Tendsto (fun n => ((toyA t)^[n] x₀).val - t.val) atTop (𝓝 0) := by
    simpa only [toyA_iterate_dist] using hgeom
  have := hshift.add_const t.val
  simpa using this

/-! ### P4 (limit fixed point via P2)

The limit of the orbit is the target, and the target is a fixed point;
together they say the level above certifies the converged value. -/

/-- The orbit's limit is a genuine fixed point of `toyA t`: the value the base
    level converges to satisfies the self-consistency equation. -/
theorem toyA_limit_fixed (t x₀ : Credence) :
    Tendsto (fun n => ((toyA t)^[n] x₀).val) atTop (𝓝 t.val) ∧ toyA t t = t :=
  ⟨toyA_contraction_tendsto t x₀, toyA_target_fixed t⟩

/-! ### P3 (degenerate seed unrecoverable): zero is absorbing

Under the product map `g x = x ⊗ e`, a zero seed stays zero forever. This is
Cromwell's rule / no ex falso, the iterated face of `conditioning_zero_any`:
impossible evidence (credence `0`) provides no constraint and never recovers
to a positive credence. -/

/-- One product step. -/
noncomputable def toyAProd (e x : Credence) : Credence := x ⊗ e

@[simp] theorem toyAProd_zero (e : Credence) : toyAProd e 0 = 0 := by
  simp only [toyAProd, zero_conj]

/-- Zero is absorbing: from a zero seed, every iterate of `g x = x ⊗ e` is
    `0`. A degenerate seed never becomes positive — Cromwell's rule. -/
theorem toyA_absorbing_zero (e : Credence) (n : ℕ) :
    (toyAProd e)^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, toyAProd_zero]

/-- The absorbing-zero orbit is exactly the unconstrained zero-evidence
    conditioning: at every step the iterate `0` is a `Conditioning 0 0`
    witness, reusing `conditioning_zero_any`. No ex falso. -/
theorem toyA_absorbing_zero_no_ex_falso (e : Credence) (n : ℕ) :
    ∃ cond : Conditioning 0 0, cond.condCred = (toyAProd e)^[n] 0 := by
  rw [toyA_absorbing_zero]
  exact conditioning_zero_any 0

end Credence

end Cred
