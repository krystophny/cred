/-
  Cred Approx: Monotonicity-Preserving Interpolation

  A pair (c₀, c₁) is monotone if c₀ ≤ c₁. The midpoint update
  Φ(c₀, c₁) = ((c₀ + c₁)/2, c₁) replaces c₀ with the average of the two
  components. We prove that Φ preserves the monotone-pair structure and that
  the swap scheme Ψ(c₀, c₁) = (c₁, c₀) does not.
-/

import Cred.Approx.Structure

namespace Cred

namespace Approx

open Credence

/-! ## Monotone pairs -/

/-- A pair of credences; the carrier for the monotone-pair structure. -/
abbrev CredPair := Credence × Credence

/-- The monotonicity predicate on pairs is classically decidable. -/
noncomputable instance instDecidableMonoPair : DecidablePred (fun q : CredPair => q.1 ≤ q.2) :=
  fun _ => Classical.dec _

/-- Monotonicity score: 1 when c₀ ≤ c₁, 0 otherwise.
    The structure that the interpolation scheme must preserve. -/
noncomputable def monoPairScore (p : CredPair) : Credence :=
  crispScore (fun q : CredPair => q.1 ≤ q.2) p

@[simp] theorem monoPairScore_one_iff (p : CredPair) :
    monoPairScore p = 1 ↔ p.1 ≤ p.2 :=
  crispScore_one_iff _ p

@[simp] theorem monoPairScore_zero_iff (p : CredPair) :
    monoPairScore p = 0 ↔ ¬ p.1 ≤ p.2 :=
  crispScore_zero_iff _ p

/-! ## Midpoint update -/

/-- Average of two credences; stays in [0,1] because each component does. -/
noncomputable def avg (a b : Credence) : Credence where
  val     := (a.val + b.val) / 2
  nonneg  := by linarith [a.nonneg, b.nonneg]
  le_one  := by linarith [a.le_one, b.le_one]

@[simp] theorem avg_val (a b : Credence) : (avg a b).val = (a.val + b.val) / 2 := rfl

/-- Midpoint update: replace the left component with the average.
    A strictly affine contraction toward the right endpoint. -/
noncomputable def midpointUpdate (p : CredPair) : CredPair :=
  (avg p.1 p.2, p.2)

/-! ## Preservation theorem -/

/-- If c₀ ≤ c₁ then (c₀ + c₁)/2 ≤ c₁, so midpointUpdate preserves monotonicity. -/
theorem midpointUpdate_preserves :
    Preserves monoPairScore midpointUpdate := by
  intro p hp
  rw [ExactPreserves_def] at *
  rw [monoPairScore_one_iff] at *
  -- hp : p.1 ≤ p.2
  -- goal : (midpointUpdate p).1 ≤ (midpointUpdate p).2
  simp only [midpointUpdate, avg_val, le_def] at hp ⊢
  linarith

/-! ## Counterexample: swap does not preserve -/

/-- Swap scheme: (c₀, c₁) ↦ (c₁, c₀). -/
def swapPair (p : CredPair) : CredPair := (p.2, p.1)

/-- A strict witness: (0, 1) is monotone but its swap (1, 0) is not. -/
theorem swapPair_not_preserves :
    ¬ Preserves monoPairScore swapPair := by
  intro h
  -- The pair (0, 1) is monotone.
  have hmono : ExactPreserves monoPairScore ((0 : Credence), (1 : Credence)) := by
    rw [ExactPreserves_def, monoPairScore_one_iff]
    simp only [le_def, zero_val, one_val, zero_le_one]
  -- Preservation would require the swap to also be monotone.
  have hswap := h _ hmono
  rw [ExactPreserves_def, monoPairScore_one_iff] at hswap
  -- But (swapPair (0, 1)) = (1, 0), which has 1 ≤ 0 — false.
  simp only [swapPair, le_def, one_val, zero_val] at hswap
  linarith

end Approx

end Cred
