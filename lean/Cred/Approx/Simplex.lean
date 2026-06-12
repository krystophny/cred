/-
  Cred Approx: Probability-Simplex Preservation (Issue #613)

  The probability simplex on `Fin n` is the crisp structure "nonnegative
  coordinates summing to one". We lift its membership predicate to a 0/1
  structure score via `crispScore`, so a stochastic update preserving the
  simplex is exactly an `Approx.Preserves` self-map of the exact-preservation
  class. A doubly-stochastic 2×2 mixing matrix is shown to preserve the
  simplex; a mass-scaling update is shown not to.

  Admissibility link: a stochastic update sends one credence assignment over
  worlds to another, keeping total mass one — the discrete analogue of
  admissible conditioning, where a row-stochastic kernel maps the prior
  simplex into itself rather than dividing by an evidence credence.
-/

import Cred.Approx.Structure
import Mathlib.Algebra.BigOperators.Fin

namespace Cred

namespace Approx

namespace Simplex

open Credence
open scoped BigOperators

/-! ## The probability simplex as a crisp structure -/

/-- Membership in the probability simplex: nonnegative coordinates of unit mass. -/
def OnSimplex {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The simplex predicate is classically decidable, so it lifts to a score. -/
noncomputable instance instDecidableOnSimplex {n : ℕ} : DecidablePred (OnSimplex (n := n)) :=
  fun _ => Classical.dec _

/-- The 0/1 structure score of the simplex. -/
noncomputable def simplexScore {n : ℕ} (p : Fin n → ℝ) : Credence :=
  crispScore OnSimplex p

@[simp] theorem simplexScore_one_iff {n : ℕ} (p : Fin n → ℝ) :
    simplexScore p = 1 ↔ OnSimplex p :=
  crispScore_one_iff OnSimplex p

/-- Exact preservation of the simplex structure is simplex membership. -/
theorem exactPreserves_simplexScore {n : ℕ} (p : Fin n → ℝ) :
    ExactPreserves (simplexScore) p ↔ OnSimplex p :=
  exactPreserves_crispScore OnSimplex p

/-! ## A doubly-stochastic 2×2 mixing update -/

/-- Mixing update on `Fin 2 → ℝ` with weight `a`: the doubly-stochastic matrix
    `[[a, 1-a], [1-a, a]]` acting on the coordinate vector. -/
def mix (a : ℝ) (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then a * p 0 + (1 - a) * p 1 else (1 - a) * p 0 + a * p 1

@[simp] theorem mix_zero (a : ℝ) (p : Fin 2 → ℝ) : mix a p 0 = a * p 0 + (1 - a) * p 1 := by
  unfold mix; rw [if_pos rfl]

@[simp] theorem mix_one (a : ℝ) (p : Fin 2 → ℝ) : mix a p 1 = (1 - a) * p 0 + a * p 1 := by
  unfold mix; rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The mixing update is mass-preserving: column sums of the matrix are one. -/
theorem mix_sum (a : ℝ) (p : Fin 2 → ℝ) : ∑ i, mix a p i = ∑ i, p i := by
  simp only [Fin.sum_univ_two, mix_zero, mix_one]
  ring

/-- For `a ∈ [0,1]` the mixing update keeps coordinates nonnegative. -/
theorem mix_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {p : Fin 2 → ℝ}
    (hp : ∀ i, 0 ≤ p i) (i : Fin 2) : 0 ≤ mix a p i := by
  have h1a : 0 ≤ 1 - a := by linarith
  fin_cases i
  · simpa only [mix_zero] using add_nonneg (mul_nonneg ha0 (hp 0)) (mul_nonneg h1a (hp 1))
  · simpa only [mix_one] using add_nonneg (mul_nonneg h1a (hp 0)) (mul_nonneg ha0 (hp 1))

/-- The mixing update maps the simplex into itself for `a ∈ [0,1]`. -/
theorem mix_onSimplex {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {p : Fin 2 → ℝ}
    (hp : OnSimplex p) : OnSimplex (mix a p) :=
  ⟨mix_nonneg ha0 ha1 hp.1, by rw [mix_sum]; exact hp.2⟩

/-- A doubly-stochastic mixing update preserves the simplex structure.

    The update sends one credence-over-worlds assignment to another of equal
    total mass: the discrete shape of admissible conditioning, which moves
    inside the prior simplex rather than dividing by an evidence credence. -/
theorem mix_preserves {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Preserves (simplexScore (n := 2)) (mix a) := by
  intro p hp
  rw [exactPreserves_simplexScore] at hp ⊢
  exact mix_onSimplex ha0 ha1 hp

/-! ## A non-stochastic update breaks the simplex -/

/-- A mass-scaling update: double every coordinate. Its column sums are two,
    so it is not stochastic. -/
def scaleTwo (p : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => 2 * p i

/-- The uniform point `(1/2, 1/2)` lies on the 2-simplex. -/
theorem uniform_onSimplex : OnSimplex (fun _ : Fin 2 => (1 : ℝ) / 2) := by
  refine ⟨fun _ => by norm_num, ?_⟩
  rw [Fin.sum_univ_two]
  norm_num

/-- The scaling update violates unit mass, hence does not preserve the simplex:
    it sends the uniform point off the simplex (its mass becomes two). -/
theorem scaleTwo_not_preserves : ¬ Preserves (simplexScore (n := 2)) scaleTwo := by
  intro hpres
  have hin : ExactPreserves (simplexScore (n := 2)) (fun _ : Fin 2 => (1 : ℝ) / 2) := by
    rw [exactPreserves_simplexScore]; exact uniform_onSimplex
  have hout := hpres _ hin
  rw [exactPreserves_simplexScore] at hout
  have hmass := hout.2
  -- the scaled mass is two, contradicting the required unit mass
  simp only [scaleTwo, Fin.sum_univ_two] at hmass
  norm_num at hmass

end Simplex

end Approx

end Cred
