/-
  Cred Math: Order, divisibility, and gcd over Nat (math-library seed)

  Clean, Mathlib-backed building blocks one notch above the parity/divisibility
  seed used by the sqrt(2) descent. These are the generic order and gcd facts
  the sqrt(3) benchmark (and later number-theory examples) lean on:
  divisibility is transitive and antisymmetric, gcd divides both arguments, and
  a common prime divisor blocks coprimality. Pure arithmetic; no measure theory.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace Cred.Math

/-! ## Order over Nat -/

/-- Strict order is transitive on `ℕ` (thin wrapper recording the fact we use). -/
theorem nat_lt_trans {a b c : ℕ} (hab : a < b) (hbc : b < c) : a < c :=
  lt_trans hab hbc

/-- Antisymmetry of `≤` on `ℕ`. -/
theorem nat_le_antisymm {a b : ℕ} (hab : a ≤ b) (hba : b ≤ a) : a = b :=
  Nat.le_antisymm hab hba

/-! ## Divisibility over Nat -/

/-- Divisibility is transitive. -/
theorem nat_dvd_trans {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c :=
  dvd_trans hab hbc

/-- A positive number divides itself, and a divisor of a positive number is at
    most that number: `a ∣ b → 0 < b → a ≤ b`. -/
theorem nat_le_of_dvd {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : a ≤ b :=
  Nat.le_of_dvd hb h

/-- Divisibility is antisymmetric: mutual divisors are equal. -/
theorem nat_dvd_antisymm {a b : ℕ} (hab : a ∣ b) (hba : b ∣ a) : a = b :=
  Nat.dvd_antisymm hab hba

/-! ## gcd over Nat -/

/-- The gcd divides the left argument. -/
theorem nat_gcd_dvd_left (a b : ℕ) : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b

/-- The gcd divides the right argument. -/
theorem nat_gcd_dvd_right (a b : ℕ) : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b

/-- A common divisor divides the gcd. -/
theorem nat_dvd_gcd {a b d : ℕ} (ha : d ∣ a) (hb : d ∣ b) : d ∣ Nat.gcd a b :=
  Nat.dvd_gcd ha hb

/-- A common prime divisor blocks coprimality: if a prime `r` divides both `a`
    and `b`, then `a` and `b` are not coprime. Generalizes the
    `not_coprime_if_both_even` step from the sqrt(2) descent to any prime. -/
theorem not_coprime_of_common_prime {a b r : ℕ} (hr : r.Prime)
    (ha : r ∣ a) (hb : r ∣ b) : ¬ Nat.Coprime a b := by
  intro hco
  have hdvd : r ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
  rw [Nat.Coprime] at hco
  rw [hco] at hdvd
  have hle : r ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd
  have hgt : 1 < r := Nat.Prime.one_lt hr
  omega

end Cred.Math
