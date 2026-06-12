/-
  Cred Math: Threshold Metric and Limit Reasoning (issue #597)

  Classical metric and limit reasoning on ℝ embeds as the crisp fragment of a
  graded layer. The classical content is mathlib's: `dist`, `Filter.Tendsto`,
  `atTop`, `𝓝`. The Cred layer adds STATUS on top: a credence-valued closeness
  `cClose x y ∈ [0,1]` and a threshold neighbourhood, giving a graded
  `TLimit f L t` reading "the sequence f is eventually t-close to L".

  WHAT IS GRADED vs THE CRISP REDUCTION.
  The graded datum is the credence `cClose x y`, which interpolates: it is 1
  exactly at coincidence (certain proximity), 0 once the distance reaches 1
  (impossible proximity), and strictly interior in between (underdetermined
  proximity at threshold t < 1). A single fixed threshold t < 1 is genuinely
  coarser than the classical limit: `TLimit f L t` only forces the tail into a
  band of radius `1 - t`, not to L. The CRISP REDUCTION is taking the meet over
  all thresholds: `(∀ t < 1, TLimit f L t) ↔ Tendsto f atTop (𝓝 L)`
  (`tlimit_all_iff_tendsto`). The classical mathlib limit is recovered exactly,
  with nothing added and nothing lost, as the t → 1 boundary of the graded
  family. The concrete `1/n → 0` example is stated through `TLimit` and tied
  back to mathlib's `tendsto_one_div_atTop_nhds_zero_nat`.
-/

import Cred.Core.Value
import Mathlib.Analysis.SpecificLimits.Basic

namespace Cred

namespace Math

open Filter Topology
open Credence

/-! ## Credence-valued closeness

The graded primitive. `cClose x y` reads the real distance `|x - y|` as a
credence: certain proximity (1) at coincidence, decaying linearly, floored at
impossibility (0) once the points are a full unit apart. -/

/-- Credence-valued closeness of two reals: `1 - min(|x - y|, 1)`. The value
    is a genuine credence in [0,1]; it is 1 iff `x = y` and 0 once `|x-y| ≥ 1`. -/
noncomputable def cClose (x y : ℝ) : Credence where
  val := 1 - min |x - y| 1
  nonneg := by
    have : min |x - y| 1 ≤ 1 := min_le_right _ _
    linarith
  le_one := by
    have : 0 ≤ min |x - y| 1 := le_min (abs_nonneg _) zero_le_one
    linarith

@[simp] theorem cClose_val (x y : ℝ) :
    (cClose x y).val = 1 - min |x - y| 1 := rfl

/-- Coincidence is certain proximity. -/
@[simp] theorem cClose_self (x : ℝ) : cClose x x = 1 := by
  ext
  simp [cClose_val]

/-- Closeness is symmetric, inheriting symmetry of the distance. -/
theorem cClose_comm (x y : ℝ) : cClose x y = cClose y x := by
  ext
  simp only [cClose_val, abs_sub_comm x y]

/-- Certain proximity holds exactly at coincidence: `cClose x y = 1 ↔ x = y`.
    This is the crisp top of the graded scale. -/
theorem cClose_eq_one_iff (x y : ℝ) : cClose x y = 1 ↔ x = y := by
  constructor
  · intro h
    have hv : (1 : ℝ) - min |x - y| 1 = 1 := congrArg Credence.val h
    have hmin : min |x - y| 1 = 0 := by linarith
    have hle : |x - y| ≤ 0 := by
      rcases min_cases |x - y| 1 with ⟨he, _⟩ | ⟨_, hlt⟩
      · rw [he] at hmin; linarith
      · linarith
    have : |x - y| = 0 := le_antisymm hle (abs_nonneg _)
    have := sub_eq_zero.mp (abs_eq_zero.mp this)
    linarith [this]
  · rintro rfl
    simp

/-- A positive threshold `t` reads off a real radius `1 - t < 1`: `t ≤ cClose x y`
    exactly when `x` and `y` lie within `1 - t` of each other. Positivity keeps
    the band radius below 1, the region where the closeness floor at distance 1
    has not yet clipped (so the unclipped distance governs the band). -/
theorem le_cClose_iff (t : Credence) (ht : 0 < t.val) (x y : ℝ) :
    t ≤ cClose x y ↔ |x - y| ≤ 1 - t.val := by
  rw [Credence.le_def, cClose_val]
  constructor
  · intro h
    have hmin : min |x - y| 1 ≤ 1 - t.val := by linarith
    rcases le_total |x - y| 1 with hle | hge
    · rwa [min_eq_left hle] at hmin
    · -- |x-y| ≥ 1 forces min = 1 ≤ 1 - t.val < 1, impossible
      rw [min_eq_right hge] at hmin; linarith
  · intro h
    have : min |x - y| 1 ≤ 1 - t.val :=
      le_trans (min_le_left _ _) h
    linarith

/-! ## Threshold neighbourhood and threshold limit -/

/-- The threshold neighbourhood of `c` at level `t`: the reals whose closeness
    to `c` reaches credence `t`. For `t < 1` this is the closed band of
    radius `1 - t`; at `t = 1` it collapses to `{c}` (`cClose_eq_one_iff`). -/
def TNhd (t : Credence) (c : ℝ) : Set ℝ := {x | t ≤ cClose c x}

theorem mem_TNhd (t : Credence) (c x : ℝ) :
    x ∈ TNhd t c ↔ t ≤ cClose c x := Iff.rfl

/-- Graded (threshold) limit: the sequence `f` is eventually t-close to `L`.
    Quantified over all thresholds `t < 1` this is the classical limit
    (`tlimit_all_iff_tendsto`); at a single fixed `t` it is strictly weaker. -/
def TLimit (f : ℕ → ℝ) (L : ℝ) (t : Credence) : Prop :=
  ∀ᶠ n in atTop, f n ∈ TNhd t L

/-! ## Classical recovery

The graded family meets the classical limit. The reduction is the meet over all
thresholds: forcing t-closeness eventually for every `t < 1` is exactly
`Tendsto`. -/

/-- CLASSICAL RECOVERY. The threshold limit at every threshold `t < 1` is the
    classical mathlib limit. The forward direction reconstructs the ε-δ tail
    by choosing a threshold `t = 1 - ε` (capped into [0,1]); the backward
    direction reads any threshold band as an ε-neighbourhood. Nothing graded
    survives the meet: the crisp fragment is precisely `Tendsto`. -/
theorem tlimit_all_iff_tendsto (f : ℕ → ℝ) (L : ℝ) :
    (∀ t : Credence, t.val < 1 → TLimit f L t) ↔ Tendsto f atTop (𝓝 L) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- band radius r ≤ 1/2 stays below 1 (positive threshold) and below ε
    set r : ℝ := min (ε / 2) (1 / 2) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
    have hr1 : r ≤ 1 / 2 := min_le_right _ _
    have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let t : Credence := ⟨1 - r, by linarith, by linarith⟩
    have htlt : t.val < 1 := by show (1 : ℝ) - r < 1; linarith
    have htpos : 0 < t.val := by show 0 < 1 - r; linarith
    have hev := h t htlt
    rw [TLimit, eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    refine ⟨N, fun n hn => ?_⟩
    have hmem := hN n hn
    rw [mem_TNhd, le_cClose_iff t htpos] at hmem
    have hband : |L - f n| ≤ r := by
      have : (1 : ℝ) - t.val = r := by show (1 : ℝ) - (1 - r) = r; ring
      rwa [this] at hmem
    rw [Real.dist_eq, abs_sub_comm]
    linarith
  · intro h t htlt
    rw [TLimit, eventually_atTop]
    rcases eq_or_lt_of_le t.nonneg with ht0 | htpos
    · -- threshold 0: closeness ≥ 0 holds everywhere, no tail condition needed
      refine ⟨0, fun n _ => ?_⟩
      rw [mem_TNhd]
      have : t = 0 := by ext; simpa using ht0.symm
      rw [this]; exact Credence.zero_le _
    · rw [Metric.tendsto_atTop] at h
      -- band radius ρ = 1 - t.val is positive; read it as an ε-neighbourhood
      set ρ : ℝ := 1 - t.val with hρ
      have hρ0 : 0 < ρ := by show 0 < 1 - t.val; linarith
      obtain ⟨N, hN⟩ := h ρ hρ0
      refine ⟨N, fun n hn => ?_⟩
      rw [mem_TNhd, le_cClose_iff t htpos]
      have hd := hN n hn
      rw [Real.dist_eq] at hd
      rw [abs_sub_comm]
      linarith [le_of_lt hd]

/-! ## Concrete limit: `1/n → 0` through the threshold notion

Stated graded, then tied back to mathlib. The threshold form holds at every
`t < 1`; collapsing the family recovers `tendsto_one_div_atTop_nhds_zero_nat`. -/

/-- The sequence `1/n` is t-close to 0 eventually, at every threshold `t < 1`. -/
theorem tlimit_one_div (t : Credence) (ht : t.val < 1) :
    TLimit (fun n : ℕ => 1 / (n : ℝ)) 0 t := by
  -- read the threshold band off the classical limit
  have hcl := tlimit_all_iff_tendsto (fun n : ℕ => 1 / (n : ℝ)) 0
  exact (hcl.mpr tendsto_one_div_atTop_nhds_zero_nat) t ht

/-- The graded `1/n → 0` collapses to the classical mathlib limit: the meet
    over all thresholds is exactly `tendsto_one_div_atTop_nhds_zero_nat`. -/
theorem tendsto_one_div_of_tlimit :
    (∀ t : Credence, t.val < 1 → TLimit (fun n : ℕ => 1 / (n : ℝ)) 0 t) ↔
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
  tlimit_all_iff_tendsto (fun n : ℕ => 1 / (n : ℝ)) 0

/-- The concrete recovery, packaged: the graded statement holds at every
    threshold and equals mathlib's `1/n → 0`. -/
theorem one_div_tlimit_and_classical :
    (∀ t : Credence, t.val < 1 → TLimit (fun n : ℕ => 1 / (n : ℝ)) 0 t) ∧
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
  ⟨fun t ht => tlimit_one_div t ht, tendsto_one_div_atTop_nhds_zero_nat⟩

end Math

end Cred
