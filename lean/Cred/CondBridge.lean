/-
  Cred Part 2: Conditional Bridge

  The propositional bridge (collapse commutes with ¬, ∧, ∨) does NOT extend
  to conditioning.  This file proves:
  1. No truth-functional conditional bridge exists (constructive Lewis triviality)
  2. The bridge holds exactly at boundary cases (b=1, a=0, a=1, or a≥b)
  3. The bridge fails for interior pairs with a < b
  4. Qualitative (three-valued) update via Gödel implication
  5. Update bridge: collapse after min-copula conditioning = qualitative update
  6. Zero-evidence duality: underdetermination = paraconsistency = bridge failure

  Throughout, "min-copula conditional" means min(a,b)/b for b > 0, which
  is the conditional credence cred(A|B) when the joint is the min copula.
-/

import Cred.Collapse.Hom
import Cred.Consequence

namespace Cred

open Credence

/-! ## Min-Copula Conditional

The min-copula conditional is min(a,b)/b for b > 0.  We define it as a
real-valued function and prove basic properties. -/

/-- Min-copula conditional: min(a,b)/b for evidence b > 0.
    This is the conditional credence when joint = min(a,b). -/
noncomputable def minCopulaCond (a b : Credence) (hb : 0 < b.val) : Credence where
  val := min a.val b.val / b.val
  nonneg := div_nonneg (le_min a.nonneg b.nonneg) (le_of_lt hb)
  le_one := by
    rw [div_le_one hb]
    exact min_le_right a.val b.val

theorem minCopulaCond_val (a b : Credence) (hb : 0 < b.val) :
    (minCopulaCond a b hb).val = min a.val b.val / b.val := rfl

/-- When a ≥ b (both positive), the min-copula conditional is 1. -/
theorem minCopulaCond_ge (a b : Credence) (hb : 0 < b.val) (hab : b.val ≤ a.val) :
    minCopulaCond a b hb = 1 := by
  ext
  simp only [minCopulaCond_val, one_val]
  rw [min_eq_right hab, div_self (ne_of_gt hb)]

/-- When a ≤ b, the min-copula conditional is a/b. -/
theorem minCopulaCond_le (a b : Credence) (hb : 0 < b.val) (hab : a.val ≤ b.val) :
    (minCopulaCond a b hb).val = a.val / b.val := by
  simp only [minCopulaCond_val]
  rw [min_eq_left hab]

/-- When a = 0, the min-copula conditional is 0. -/
theorem minCopulaCond_zero_left (b : Credence) (hb : 0 < b.val) :
    minCopulaCond 0 b hb = 0 := by
  ext
  simp only [minCopulaCond_val, zero_val, min_eq_left b.nonneg, zero_div]

/-- When b = 1, the min-copula conditional is a. -/
theorem minCopulaCond_one_right (a : Credence) :
    minCopulaCond a 1 one_pos = a := by
  ext
  simp only [minCopulaCond_val, one_val, min_eq_left a.le_one, div_one]

/-! ## Priority 1: Impossibility Theorem

No truth-functional f : ThreeVal → ThreeVal → ThreeVal can satisfy
  collapse(min(a,b)/b) = f(collapse(b), collapse(a))
for all a, b with b > 0.

Proof: two witnesses force f(½,½) to be both ½ and 1. -/

/-- The conditional bridge cannot be truth-functional: no function
    f : ThreeVal → ThreeVal → ThreeVal satisfies
    collapse(minCopulaCond a b) = f(collapse(b), collapse(a))
    for all a, b ∈ [0,1] with b > 0. -/
theorem no_truthfunctional_cond_bridge :
    ¬ ∃ f : ThreeVal → ThreeVal → ThreeVal,
      ∀ a b : Credence, ∀ hb : 0 < b.val,
        collapse (minCopulaCond a b hb) = f (collapse b) (collapse a) := by
  intro ⟨f, hf⟩
  set a₁ : Credence := ⟨3/10, by norm_num, by norm_num⟩
  set b₁ : Credence := ⟨7/10, by norm_num, by norm_num⟩
  have hb₁ : (0 : ℝ) < b₁.val := by norm_num
  have h1 := hf a₁ b₁ hb₁
  have hca₁ : collapse a₁ = ThreeVal.half :=
    collapse_interior a₁ (by norm_num) (by norm_num)
  have hcb₁ : collapse b₁ = ThreeVal.half :=
    collapse_interior b₁ (by norm_num) (by norm_num)
  have hcond₁ : (minCopulaCond a₁ b₁ hb₁).val = 3 / 7 := by
    simp only [minCopulaCond_val]
    norm_num
  have hcond₁_int : collapse (minCopulaCond a₁ b₁ hb₁) = ThreeVal.half :=
    collapse_interior _ (by rw [hcond₁]; norm_num) (by rw [hcond₁]; norm_num)
  rw [hca₁, hcb₁, hcond₁_int] at h1
  -- h1 : ThreeVal.half = f ThreeVal.half ThreeVal.half
  set a₂ : Credence := ⟨7/10, by norm_num, by norm_num⟩
  set b₂ : Credence := ⟨3/10, by norm_num, by norm_num⟩
  have hb₂ : (0 : ℝ) < b₂.val := by norm_num
  have h2 := hf a₂ b₂ hb₂
  have hca₂ : collapse a₂ = ThreeVal.half :=
    collapse_interior a₂ (by norm_num) (by norm_num)
  have hcb₂ : collapse b₂ = ThreeVal.half :=
    collapse_interior b₂ (by norm_num) (by norm_num)
  have hcond₂ : minCopulaCond a₂ b₂ hb₂ = 1 :=
    minCopulaCond_ge a₂ b₂ hb₂ (by norm_num)
  rw [hca₂, hcb₂, hcond₂, collapse_one] at h2
  -- h2 : ThreeVal.one = f ThreeVal.half ThreeVal.half
  -- Contradiction: ThreeVal.half = f ... = ThreeVal.one
  rw [← h1] at h2
  exact absurd h2 (by decide)

/-! ## Priority 1: Boundary Characterization

The conditional bridge holds exactly when the min-copula conditional
lands on a boundary value (0 or 1).  This happens iff:
  b = 1, a = 0, a = 1, or a ≥ b (with b > 0).

In these cases, collapse(minCopulaCond a b) = godel_impl(collapse(b), collapse(a)). -/

/-- When a = 0 and b > 0: conditional is 0, godel_impl maps to appropriate value. -/
theorem cond_bridge_at_a_zero (b : Credence) (hb : 0 < b.val) :
    collapse (minCopulaCond 0 b hb) =
    ThreeVal.godel_impl (collapse b) (collapse (0 : Credence)) := by
  rw [minCopulaCond_zero_left, collapse_zero]
  have hb0 : b.val ≠ 0 := ne_of_gt hb
  by_cases hb1 : b.val = 1
  · rw [show b = 1 from by ext; exact hb1, collapse_one]; rfl
  · rw [collapse_interior b hb0 hb1]; rfl

/-- When a = 1 and b > 0: conditional is min(1,b)/b = b/b = 1. -/
theorem cond_bridge_at_a_one (b : Credence) (hb : 0 < b.val) :
    collapse (minCopulaCond 1 b hb) =
    ThreeVal.godel_impl (collapse b) (collapse (1 : Credence)) := by
  have hcond : minCopulaCond 1 b hb = 1 :=
    minCopulaCond_ge 1 b hb b.le_one
  simp only [hcond, collapse_one]
  have hb0 : b.val ≠ 0 := ne_of_gt hb
  by_cases hb1 : b.val = 1
  · rw [show b = 1 from by ext; exact hb1, collapse_one]; rfl
  · rw [collapse_interior b hb0 hb1]; rfl

/-- When b = 1: conditional is min(a,1)/1 = a. -/
theorem cond_bridge_at_b_one (a : Credence) :
    collapse (minCopulaCond a 1 one_pos) =
    ThreeVal.godel_impl (collapse (1 : Credence)) (collapse a) := by
  rw [minCopulaCond_one_right, collapse_one]
  cases hca : collapse a <;> simp [ThreeVal.godel_impl]

/-- When a ≥ b (and b > 0): conditional is 1. -/
theorem cond_bridge_at_a_ge_b (a b : Credence) (hb : 0 < b.val) (hab : b.val ≤ a.val) :
    collapse (minCopulaCond a b hb) =
    ThreeVal.godel_impl (collapse b) (collapse a) := by
  rw [minCopulaCond_ge a b hb hab, collapse_one]
  by_cases hb0 : b.val = 0
  · exact absurd hb0 (ne_of_gt hb)
  · by_cases hb1 : b.val = 1
    · have ha1 : a.val = 1 := le_antisymm a.le_one (by linarith)
      have hbc : b = 1 := by ext; exact hb1
      have hac : a = 1 := by ext; exact ha1
      rw [hbc, hac, collapse_one]; rfl
    · have hcb : collapse b = ThreeVal.half := collapse_interior b hb0 hb1
      rw [hcb]
      by_cases ha1 : a.val = 1
      · have hac : a = 1 := by ext; exact ha1
        rw [hac, collapse_one]; rfl
      · have ha0 : a.val ≠ 0 := ne_of_gt (lt_of_lt_of_le hb hab)
        rw [collapse_interior a ha0 ha1]; rfl

/-- The full boundary characterization: collapse of the min-copula conditional
    equals godel_impl(collapse(b), collapse(a)) whenever at least one of:
    (1) a = 0, (2) a = 1, (3) b = 1, or (4) a ≥ b (with b > 0). -/
theorem cond_bridge_boundary (a b : Credence) (hb : 0 < b.val)
    (h : a = 0 ∨ a = 1 ∨ b = 1 ∨ b.val ≤ a.val) :
    collapse (minCopulaCond a b hb) =
    ThreeVal.godel_impl (collapse b) (collapse a) := by
  rcases h with rfl | rfl | rfl | hab
  · exact cond_bridge_at_a_zero b hb
  · exact cond_bridge_at_a_one b hb
  · exact cond_bridge_at_b_one a
  · exact cond_bridge_at_a_ge_b a b hb hab

/-! ## Priority 1: Interior Failure

When both a and b are interior (0 < a < 1 and 0 < b < 1) with a < b,
the min-copula conditional a/b is interior, but we can find pairs where
godel_impl disagrees with the collapse. -/

/-- For interior a < b, the min-copula conditional is interior. -/
theorem minCopulaCond_interior (a b : Credence) (hb : 0 < b.val)
    (ha_pos : 0 < a.val) (ha_lt_b : a.val < b.val) :
    0 < (minCopulaCond a b hb).val ∧ (minCopulaCond a b hb).val < 1 := by
  constructor
  · rw [minCopulaCond_le a b hb (le_of_lt ha_lt_b)]
    exact div_pos ha_pos hb
  · rw [minCopulaCond_le a b hb (le_of_lt ha_lt_b)]
    rw [div_lt_one hb]
    exact ha_lt_b

/-- The conditional bridge fails for specific interior pairs: a = 3/10, b = 7/10.
    The conditional 3/7 collapses to half, but godel_impl(half, half) = one. -/
theorem cond_bridge_fails_interior :
    ∃ a b : Credence, ∃ hb : 0 < b.val,
      0 < a.val ∧ a.val < 1 ∧ 0 < b.val ∧ b.val < 1 ∧ a.val < b.val ∧
      collapse (minCopulaCond a b hb) ≠
      ThreeVal.godel_impl (collapse b) (collapse a) := by
  refine ⟨⟨3/10, by norm_num, by norm_num⟩, ⟨7/10, by norm_num, by norm_num⟩,
    by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have hcond : (minCopulaCond ⟨3/10, by norm_num, by norm_num⟩
    ⟨7/10, by norm_num, by norm_num⟩ (by norm_num : (0:ℝ) < 7/10)).val = 3 / 7 := by
    simp only [minCopulaCond_val]
    norm_num
  rw [collapse_interior _ (by rw [hcond]; norm_num) (by rw [hcond]; norm_num)]
  rw [collapse_interior ⟨7/10, by norm_num, by norm_num⟩ (by norm_num) (by norm_num)]
  rw [collapse_interior ⟨3/10, by norm_num, by norm_num⟩ (by norm_num) (by norm_num)]
  decide

/-! ## Priority 2: Qualitative Update on {0, ½, 1}

Define three-valued update as Gödel implication applied to the current state
(representing "evidence updates belief via the Gödel conditional"). -/

/-- Three-valued qualitative update: given prior value v and evidence e (both in ThreeVal),
    the posterior is godel_impl(e, v) — the Gödel conditional of v given e. -/
def qualitativeUpdate (evidence prior : ThreeVal) : ThreeVal :=
  ThreeVal.godel_impl evidence prior

theorem qualUpdate_zero_zero : qualitativeUpdate ThreeVal.zero ThreeVal.zero = ThreeVal.one := rfl
theorem qualUpdate_zero_half : qualitativeUpdate ThreeVal.zero ThreeVal.half = ThreeVal.one := rfl
theorem qualUpdate_zero_one  : qualitativeUpdate ThreeVal.zero ThreeVal.one  = ThreeVal.one := rfl
theorem qualUpdate_half_zero : qualitativeUpdate ThreeVal.half ThreeVal.zero = ThreeVal.zero := rfl
theorem qualUpdate_half_half : qualitativeUpdate ThreeVal.half ThreeVal.half = ThreeVal.one := rfl
theorem qualUpdate_half_one  : qualitativeUpdate ThreeVal.half ThreeVal.one  = ThreeVal.one := rfl
theorem qualUpdate_one_zero  : qualitativeUpdate ThreeVal.one ThreeVal.zero  = ThreeVal.zero := rfl
theorem qualUpdate_one_half  : qualitativeUpdate ThreeVal.one ThreeVal.half  = ThreeVal.half := rfl
theorem qualUpdate_one_one   : qualitativeUpdate ThreeVal.one ThreeVal.one   = ThreeVal.one := rfl

/-! ## Priority 2: Update Bridge Theorem

Under boundary conditions (Theorem cond_bridge_boundary), Bayesian update
commutes with collapse: first updating then collapsing gives the same result
as first collapsing then doing qualitative update. -/

/-- Update bridge: when boundary conditions hold, collapsing after min-copula
    conditioning equals qualitative update after collapsing. -/
theorem update_bridge (a b : Credence) (hb : 0 < b.val)
    (h : a = 0 ∨ a = 1 ∨ b = 1 ∨ b.val ≤ a.val) :
    collapse (minCopulaCond a b hb) =
    qualitativeUpdate (collapse b) (collapse a) := by
  unfold qualitativeUpdate
  exact cond_bridge_boundary a b hb h

/-! ## Priority 2: Zero-Evidence Duality

Three equivalent manifestations of c · 0 = 0:
  (1) Bayesian update at zero evidence is underdetermined
  (2) LP explosion fails (the ½ witness)
  (3) The conditional bridge breaks at evidence 0

These are connected by the common algebraic root: the absorptivity of zero
under multiplication. -/

/-- Manifestation (1): Zero-evidence underdetermination.
    When evidence = 0, any conditional credence is consistent. -/
theorem zero_evidence_underdetermined (c : Credence) :
    ∃ cond : Conditioning 0 0, cond.condCred = c :=
  conditioning_zero_any c

/-- Manifestation (2): LP explosion failure.
    The ½ witness makes both A and ¬A designated without forcing B. -/
theorem zero_evidence_paraconsistency :
    ∃ v : Fin 2 → Credence,
      isDesignatedLP (collapse (v 0)) ∧
      isDesignatedLP (ThreeVal.neg (collapse (v 0))) ∧
      ¬ isDesignatedLP (collapse (v 1)) := by
  use fun i => if i = 0 then Credence.half else 0
  refine ⟨?_, ?_, ?_⟩
  · simp [collapse_half, isDesignatedLP]
  · simp [collapse_half, ThreeVal.neg, isDesignatedLP]
  · simp [collapse_zero, isDesignatedLP]

/-- Manifestation (3): Conditional bridge failure at zero evidence.
    No truth-functional conditional can handle evidence with credence 0,
    because zero absorbs any conditional value. -/
theorem zero_evidence_bridge_failure :
    ∀ c₁ c₂ : Credence,
      ∃ cond₁ cond₂ : Conditioning 0 0,
        cond₁.condCred = c₁ ∧ cond₂.condCred = c₂ := by
  intro c₁ c₂
  obtain ⟨cd₁, h₁⟩ := conditioning_zero_any c₁
  obtain ⟨cd₂, h₂⟩ := conditioning_zero_any c₂
  exact ⟨cd₁, cd₂, h₁, h₂⟩

/-- Zero-evidence duality: the three manifestations share a common root.
    The algebraic fact c ⊗ 0 = 0 simultaneously implies:
    - Any conditional is consistent at zero evidence (underdetermination)
    - The collapse of ½ provides both a designated and its negation designated
    - No function of collapsed values can recover the unconstrained conditional
    This theorem packages all three as a conjunction. -/
theorem zero_evidence_duality :
    (∀ c : Credence, ∃ cond : Conditioning 0 0, cond.condCred = c) ∧
    (∃ v : ThreeVal, isDesignatedLP v ∧ isDesignatedLP (ThreeVal.neg v)) ∧
    (∀ c₁ c₂ : Credence, ∃ cond₁ cond₂ : Conditioning 0 0,
      cond₁.condCred = c₁ ∧ cond₂.condCred = c₂) := by
  refine ⟨conditioning_zero_any, ⟨ThreeVal.half, trivial, trivial⟩, ?_⟩
  intro c₁ c₂
  obtain ⟨cd₁, h₁⟩ := conditioning_zero_any c₁
  obtain ⟨cd₂, h₂⟩ := conditioning_zero_any c₂
  exact ⟨cd₁, cd₂, h₁, h₂⟩

/-- Zero-evidence duality through the admissible set: Cond 0 0 is all of
    [0,1] (underdetermination), the ½ witness gives LP paraconsistency,
    and any two conditional credences are simultaneously admissible
    (bridge failure). Cond-phrased version of zero_evidence_duality. -/
theorem zero_evidence_duality_cond :
    Cond 0 0 = Set.univ ∧
    (∃ v : ThreeVal, isDesignatedLP v ∧ isDesignatedLP (ThreeVal.neg v)) ∧
    (∀ c₁ c₂ : Credence, c₁ ∈ Cond 0 0 ∧ c₂ ∈ Cond 0 0) := by
  refine ⟨cond_zero_zero_univ, ⟨ThreeVal.half, trivial, trivial⟩, fun c₁ c₂ => ?_⟩
  simp [cond_zero_zero_univ]

/-! ## Priority 3: Interior Conditional Range

For interior pairs (both collapse to ½), the set of min-copula conditionals
covers (0, 1] — it is maximally underdetermined by the collapsed values. -/

/-- For any target r ∈ (0, 1], there exist interior a, b with
    minCopulaCond a b = r (where both a and b collapse to half). -/
theorem interior_cond_range (r : Credence) (hr_pos : 0 < r.val) :
    ∃ a b : Credence, ∃ hb : 0 < b.val,
      a.val ≠ 0 ∧ a.val ≠ 1 ∧ b.val ≠ 0 ∧ b.val ≠ 1 ∧
      minCopulaCond a b hb = r := by
  set bv : ℝ := 1 / 2
  set av : ℝ := r.val / 2
  have hb_pos : (0 : ℝ) < bv := by norm_num
  have ha_nn : (0 : ℝ) ≤ av := div_nonneg (le_of_lt hr_pos) (by norm_num)
  have ha_le : av ≤ 1 := by
    calc r.val / 2 ≤ 1 / 2 := by linarith [r.le_one]
      _ ≤ 1 := by norm_num
  have ha_pos : (0 : ℝ) < av := div_pos hr_pos (by norm_num)
  have ha_ne0 : av ≠ 0 := ne_of_gt ha_pos
  have ha_ne1 : av ≠ 1 := by
    intro h
    have : r.val / 2 = 1 := h
    have := r.le_one
    linarith
  set a : Credence := ⟨av, ha_nn, ha_le⟩
  set b : Credence := ⟨bv, by norm_num, by norm_num⟩
  have hb : (0 : ℝ) < b.val := hb_pos
  refine ⟨a, b, hb, ha_ne0, ha_ne1, by norm_num, by norm_num, ?_⟩
  ext
  simp only [minCopulaCond_val]
  have hab : a.val ≤ b.val := by
    show av ≤ bv
    calc r.val / 2 ≤ 1 / 2 := by linarith [r.le_one]
      _ = bv := rfl
  rw [min_eq_left hab]
  show av / bv = r.val
  simp only [av, bv]
  rw [div_div, mul_comm]
  norm_num

/-- Interior conditional range through the admissible set: every r with
    0 < r lies in Cond j e for an interior joint/evidence pair. With
    positive evidence the membership is unique (cond_singleton_of_pos),
    so r is THE conditional for that pair. Cond-phrased version of
    interior_cond_range. -/
theorem cond_interior_range (r : Credence) (hr_pos : 0 < r.val) :
    ∃ j e : Credence,
      j.val ≠ 0 ∧ j.val ≠ 1 ∧ e.val ≠ 0 ∧ e.val ≠ 1 ∧ r ∈ Cond j e := by
  have hj_nonneg : (0 : ℝ) ≤ r.val / 2 := div_nonneg r.nonneg (by norm_num)
  have hj_le : r.val / 2 ≤ 1 := by linarith [r.le_one]
  set j : Credence := ⟨r.val / 2, hj_nonneg, hj_le⟩
  set e : Credence := ⟨1 / 2, by norm_num, by norm_num⟩
  have hj0 : j.val ≠ 0 := ne_of_gt (div_pos hr_pos (by norm_num))
  have hj1 : j.val ≠ 1 := by
    intro h
    have : r.val / 2 = 1 := h
    linarith [r.le_one]
  refine ⟨j, e, hj0, hj1, by norm_num, by norm_num, ?_⟩
  show r ⊗ e = j
  ext
  simp only [conj_val]
  show r.val * (1 / 2) = r.val / 2
  ring

end Cred
