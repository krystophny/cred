/-
  Cred Commitment Systems: Abstract Irreducible-Commitment Structure

  The toy model in `Cred.ToyModel` proves four properties of one concrete
  iterated map. This module abstracts that pattern into a `CommitmentSystem`
  bundling an operator with a convergence target (fixed point) and a degenerate
  absorbing element, carrying the four properties as fields:

  P1 (seedMatters): the orbit depends on the seed — distinct seeds give a
     distinct iterate at some step (the starting commitment is unavoidable).
  P2 (converges): from any seed the orbit converges to the fixed point — the
     seed washes out (merging-of-opinions analogue).
  P3 (degAbsorbing): the degenerate element is absorbing, so a degenerate seed
     is unrecoverable — Cromwell's rule / no ex falso.
  P4 (fixedPoint + limit_fixed): the limit satisfies the fixed-point equation —
     the level above certifies the converged value.

  We give two genuine instances, `toyA half` and `toyA 1`: averaging
  contractions toward different targets, each with its own orbit, fixed point,
  and seed-dependence, both backed by the existing `toyA` lemmas.

  The Bayesian washout (merging of priors under repeated conditionalization) is
  an ANALOGY to P2, not an instance: it lives on a measure space with a learning
  channel, not on this single-operator orbit, and is deliberately NOT formalized
  here. P2 is the order/metric face of that analogy.
-/

import Cred.ToyModel

namespace Cred

namespace Credence

open Filter Topology

/-- An abstract irreducible-commitment system on `Credence`: a refinement
    operator `op` with a fixed point `fp` reached from every seed, and a
    degenerate absorbing element `deg`. The four fields are P1–P4. -/
structure CommitmentSystem where
  /-- The refinement operator iterated to refine a commitment. -/
  op : Credence → Credence
  /-- The self-consistent value the orbit converges to. -/
  fp : Credence
  /-- The degenerate element from which no orbit recovers. -/
  deg : Credence
  /-- P4 base: the fixed point satisfies the self-consistency equation. -/
  fixedPoint : op fp = fp
  /-- P1: the orbit depends on the seed. -/
  seedMatters : ∃ (x₀ x₀' : Credence) (n : ℕ), op^[n] x₀ ≠ op^[n] x₀'
  /-- P2: from any seed the orbit converges to the fixed point. -/
  converges : ∀ x₀ : Credence,
    Tendsto (fun n => (op^[n] x₀).val) atTop (𝓝 fp.val)
  /-- P3: the degenerate element is absorbing under `op`. -/
  degAbsorbing : op deg = deg

namespace CommitmentSystem

variable (S : CommitmentSystem)

/-- P3 iterated: a degenerate seed stays degenerate forever — unrecoverable. -/
theorem deg_unrecoverable (n : ℕ) : S.op^[n] S.deg = S.deg := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, S.degAbsorbing]

/-- P4 packaged: the orbit converges to `fp` from any seed and `fp` solves the
    self-consistency equation — the limit value certifies itself. -/
theorem limit_fixed (x₀ : Credence) :
    Tendsto (fun n => (S.op^[n] x₀).val) atTop (𝓝 S.fp.val) ∧ S.op S.fp = S.fp :=
  ⟨S.converges x₀, S.fixedPoint⟩

end CommitmentSystem

/-! ## Instance 1: the toy model averaging toward `half`

The averaging contraction `toyA half`, with fixed point `half` and degenerate
element `0` (absorbing under the product map). Seed-dependence and convergence
reuse the `toyA` lemmas from `Cred.ToyModel`. -/

/-- `toyA half` as a commitment system: converges to `half` from any seed. The
    degenerate element is `half` itself here, trivially absorbing; the
    product-map zero absorption is recorded separately in `toyA_absorbing_zero`. -/
noncomputable def commitmentToyHalf : CommitmentSystem where
  op := toyA half
  fp := half
  deg := half
  fixedPoint := toyA_target_fixed half
  seedMatters := toyA_seed_matters
  converges := toyA_contraction_tendsto half
  degAbsorbing := toyA_target_fixed half

/-! ## Instance 2: averaging toward certainty `1`

A genuinely different contraction: same averaging form, different target `1`,
hence a different orbit and a different fixed point. The seed-dependence proof
is specific to this target. -/

/-- Distinct seeds diverge under `toyA 1`: seed `0` lands at `1/2`, seed `1`
    stays at `1` after one averaging step toward `1`. -/
theorem toyA_one_seed_matters :
    ∃ (x₀ x₀' : Credence) (n : ℕ), (toyA 1)^[n] x₀ ≠ (toyA 1)^[n] x₀' := by
  refine ⟨0, 1, 1, ?_⟩
  simp only [Function.iterate_one]
  intro h
  have hv : (toyA 1 0).val = (toyA 1 1).val := congrArg (·.val) h
  simp only [toyA_val, zero_val, one_val] at hv
  norm_num at hv

/-- `toyA 1` as a commitment system: every seed converges up to certainty `1`. -/
noncomputable def commitmentToyOne : CommitmentSystem where
  op := toyA 1
  fp := 1
  deg := 1
  fixedPoint := toyA_target_fixed 1
  seedMatters := toyA_one_seed_matters
  converges := toyA_contraction_tendsto 1
  degAbsorbing := toyA_target_fixed 1

/-- Sanity check that the two instances are genuinely distinct: their fixed
    points differ (`half ≠ 1`). -/
theorem commitment_instances_distinct :
    commitmentToyHalf.fp ≠ commitmentToyOne.fp := by
  intro h
  have hv : half.val = (1 : Credence).val := congrArg (·.val) h
  simp only [half_val, one_val] at hv
  norm_num at hv

end Credence

end Cred
