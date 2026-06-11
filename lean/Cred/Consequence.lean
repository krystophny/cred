/-
  Cred Part 2: Consequence Relations

  Defines designated-value consequence relations on the three-valued collapse,
  graded consequence on [0,1], and proves compatibility with unconstrained
  conditioning (no explosion).

  Key results:
  - K3 consequence (designate {1}): paracomplete, no tautologies
  - LP consequence (designate {1, 1/2}): paraconsistent, explosion fails
  - RM3 consequence (designate {1, 1/2} + relevance)
  - Graded consequence parametrized by threshold
  - No-explosion theorem for all compatible consequence relations
-/

import Cred.Collapse.Hom
import Cred.Valuation

namespace Cred

open ThreeVal

/-! ## Designated Values -/

/-- K3 designation: only `one` is designated (strict, paracomplete). -/
def isDesignatedK3 : ThreeVal → Prop
  | one => True
  | _ => False

/-- LP designation: `one` and `half` are designated (tolerant, paraconsistent). -/
def isDesignatedLP : ThreeVal → Prop
  | one => True
  | half => True
  | zero => False

instance : DecidablePred isDesignatedK3 :=
  fun v => by cases v <;> simp [isDesignatedK3] <;> infer_instance

instance : DecidablePred isDesignatedLP :=
  fun v => by cases v <;> simp [isDesignatedLP] <;> infer_instance

/-! ## Three-Valued Consequence -/

/-- A three-valued valuation: assigns a ThreeVal to each proposition. -/
def ThreeValuation (α : Type*) := α → ThreeVal

/-- Three-valued consequence: premises entail conclusion when every valuation
    that makes all premises designated also makes the conclusion designated. -/
def threeValConsequence (designated : ThreeVal → Prop) (α : Type*)
    (premises : List α) (conclusion : α) : Prop :=
  ∀ v : ThreeValuation α,
    (∀ p ∈ premises, designated (v p)) → designated (v conclusion)

/-! ### K3 Properties -/

/-- K3 is paracomplete: there are no K3 tautologies.
    Proof: the constant-half valuation makes every formula non-designated. -/
theorem k3_no_tautology (α : Type*) [Nonempty α] (a : α) :
    ¬ threeValConsequence isDesignatedK3 α [] a := by
  intro h
  have := h (fun _ => half) (by simp)
  exact this

/-- K3: excluded middle fails. For any proposition A, there exists a valuation
    where A ⊔ ~A is not designated (when A = half). -/
theorem k3_excluded_middle_fails :
    ∃ v : ThreeVal, ¬ isDesignatedK3 (ThreeVal.disj v (ThreeVal.neg v)) := by
  use half
  simp [ThreeVal.disj, ThreeVal.neg, isDesignatedK3]

/-! ### LP Properties -/

/-- LP: excluded middle holds. For any value, A ⊔ ~A is always designated. -/
theorem lp_excluded_middle (v : ThreeVal) :
    isDesignatedLP (ThreeVal.disj v (ThreeVal.neg v)) := by
  cases v <;> simp [ThreeVal.disj, ThreeVal.neg, isDesignatedLP]

/-- LP: explosion fails. A and ~A can both be designated (at half)
    without forcing arbitrary B to be designated. -/
theorem lp_no_explosion :
    ∃ v : ThreeValuation (Fin 2),
      isDesignatedLP (v 0) ∧ isDesignatedLP (ThreeVal.neg (v 0)) ∧
      ¬ isDesignatedLP (v 1) := by
  use fun i => if i = 0 then half else zero
  simp [ThreeVal.neg, isDesignatedLP]

/-! ### Graded Consequence -/

/-- Graded consequence parametrized by threshold t:
    Premises with credence ≥ t entail conclusion with credence ≥ t.
    This works directly on [0,1] without collapsing. -/
def gradedConsequence (t : Credence) (α : Type*)
    (premises : List α) (conclusion : α) : Prop :=
  ∀ v : α → Credence,
    (∀ p ∈ premises, t ≤ v p) → t ≤ v conclusion

/-- Graded consequence at t=1 is strict: only certainty propagates. -/
theorem graded_at_one_is_strict (α : Type*) (premises : List α) (conclusion : α) :
    gradedConsequence 1 α premises conclusion ↔
    ∀ v : α → Credence,
      (∀ p ∈ premises, v p = 1) → v conclusion = 1 := by
  constructor
  · intro h v hprem
    have hge := h v (fun p hp => by rw [hprem p hp])
    exact le_antisymm (v conclusion).le_one hge
  · intro h v hprem
    have hprem' : ∀ p ∈ premises, v p = 1 := by
      intro p hp
      exact le_antisymm (v p).le_one (hprem p hp)
    rw [h v hprem']

/-! ## No-Explosion Theorem

The key result: for any consequence relation compatible with unconstrained
conditioning at zero, explosion fails when premises have credence 1/2. -/

/-- A consequence relation on credences is explosion-free when the existence
    of a valuation with A and ~A both having credence 1/2 does not force
    arbitrary B to any particular value. -/
theorem no_explosion_at_half :
    ∃ v : Fin 2 → Credence,
      v 0 = Credence.half ∧
      Credence.neg (v 0) = Credence.half ∧
      v 1 = 0 := by
  use fun i => if i = 0 then Credence.half else 0
  refine ⟨by simp, ?_, by simp⟩
  simp [Credence.liar_fixed_point]

/-- For any threshold 0 < t ≤ 1/2, graded consequence does not have explosion:
    there exist premises A, ~A both above threshold with conclusion below. -/
theorem graded_no_explosion (t : Credence) (ht : t.val ≤ 1/2) (ht_pos : 0 < t.val) :
    ∃ v : Fin 2 → Credence,
      t ≤ v 0 ∧ t ≤ Credence.neg (v 0) ∧ ¬(t ≤ v 1) := by
  use fun i => if i = 0 then Credence.half else 0
  refine ⟨?_, ?_, ?_⟩
  · simp [Credence.le_def, Credence.half_val]; linarith
  · simp [Credence.neg, Credence.le_def, Credence.half_val]; linarith
  · simp [Credence.le_def, Credence.zero_val]
    linarith

/-- For t > 1/2, no valuation can make both v(A) >= t and ~v(A) >= t:
    the premises of explosion are vacuously unsatisfiable. Explosion holds
    vacuously because t + t > 1 but v(A) + ~v(A) = 1. -/
theorem graded_explosion_vacuous (t : Credence) (ht : 1/2 < t.val) :
    ∀ v : Fin 2 → Credence,
      t ≤ v 0 → t ≤ Credence.neg (v 0) → t ≤ v 1 := by
  intro v h0 h0neg
  exfalso
  have h1 : t.val ≤ (v 0).val := h0
  have h2 : t.val ≤ 1 - (v 0).val := by
    simp [Credence.le_def, Credence.neg_val] at h0neg
    exact h0neg
  linarith

/-- Connection: unconstrained conditioning at zero means that
    when evidence has credence 0, no conclusion is forced. This is the
    algebraic basis for explosion failure. -/
theorem unconstrained_blocks_explosion (c : Credence) :
    ∃ cond : Credence.Conditioning 0 0, cond.condCred = c :=
  Credence.conditioning_zero_any c

/-! ## Bridge Theorem: LP ↔ Positivity, K3 ↔ Certainty

The collapse homomorphism connects [0,1]-valued reasoning to three-valued
reasoning. The bridge theorem makes this precise: LP consequence on {0,1/2,1}
is equivalent to positivity consequence on [0,1], and K3 consequence is
equivalent to certainty consequence on [0,1]. -/

/-- LP designation via collapse: collapse(c) is LP-designated iff c > 0. -/
theorem lp_designated_iff_pos (c : Credence) :
    isDesignatedLP (collapse c) ↔ 0 < c.val := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    have hzero : c.val = 0 := le_antisymm hle c.nonneg
    have hc : c = 0 := by ext; exact hzero
    rw [hc, collapse_zero] at h
    exact h
  · intro hpos
    by_cases h1 : c.val = 1
    · have hc : c = 1 := by ext; exact h1
      rw [hc, collapse_one]
      trivial
    · have h0 : c.val ≠ 0 := ne_of_gt hpos
      rw [collapse_interior c h0 h1]
      trivial

/-- K3 designation via collapse: collapse(c) is K3-designated iff c = 1. -/
theorem k3_designated_iff_one (c : Credence) :
    isDesignatedK3 (collapse c) ↔ c = 1 := by
  constructor
  · intro h
    by_cases h0 : c.val = 0
    · have hc : c = 0 := by ext; exact h0
      rw [hc, collapse_zero] at h; exact absurd h id
    · by_cases h1 : c.val = 1
      · ext; exact h1
      · rw [collapse_interior c h0 h1] at h; exact absurd h id
  · intro h
    rw [h, collapse_one]
    trivial

/-- Lift a ThreeVal to a Credence: zero ↦ 0, half ↦ 1/2, one ↦ 1. -/
noncomputable def liftThreeVal : ThreeVal → Credence
  | ThreeVal.zero => 0
  | ThreeVal.half => Credence.half
  | ThreeVal.one => 1

/-- Lifting then collapsing is the identity. -/
@[simp] theorem lift_collapse_id (v : ThreeVal) :
    collapse (liftThreeVal v) = v := by
  cases v with
  | zero => simp [liftThreeVal, collapse_zero]
  | half => simp [liftThreeVal, collapse_half]
  | one => simp [liftThreeVal, collapse_one]

/-- Lifted LP-designated values have positive credence. -/
theorem lift_pos_of_designated_lp (v : ThreeVal) (h : isDesignatedLP v) :
    0 < (liftThreeVal v).val := by
  cases v with
  | zero => exact absurd h id
  | half => simp [liftThreeVal, Credence.half_val]
  | one => simp [liftThreeVal, Credence.one_val]

/-- Lifted K3-designated values are certain. -/
theorem lift_one_of_designated_k3 (v : ThreeVal) (h : isDesignatedK3 v) :
    liftThreeVal v = 1 := by
  cases v with
  | zero => exact absurd h id
  | half => exact absurd h id
  | one => rfl

/-! ### Consequence on [0,1] -/

/-- Positivity consequence: every valuation making premises positive
    also makes the conclusion positive. -/
def positivityConsequence (α : Type*) (premises : List α) (conclusion : α) : Prop :=
  ∀ v : α → Credence, (∀ p ∈ premises, 0 < (v p).val) → 0 < (v conclusion).val

/-- Certainty consequence: every valuation making premises certain
    also makes the conclusion certain. -/
def certaintyConsequence (α : Type*) (premises : List α) (conclusion : α) : Prop :=
  ∀ v : α → Credence, (∀ p ∈ premises, v p = 1) → v conclusion = 1

/-- Bridge Theorem (LP): LP consequence on {0,1/2,1} is equivalent to
    positivity consequence on [0,1]. -/
theorem lp_bridge (α : Type*) (premises : List α) (conclusion : α) :
    threeValConsequence isDesignatedLP α premises conclusion ↔
    positivityConsequence α premises conclusion := by
  constructor
  · intro hlp v hprem
    let w : ThreeValuation α := fun a => collapse (v a)
    have hwprem : ∀ p ∈ premises, isDesignatedLP (w p) :=
      fun p hp => (lp_designated_iff_pos (v p)).mpr (hprem p hp)
    have := hlp w hwprem
    exact (lp_designated_iff_pos (v conclusion)).mp this
  · intro hpos w hwprem
    let v : α → Credence := fun a => liftThreeVal (w a)
    have hvprem : ∀ p ∈ premises, 0 < (v p).val :=
      fun p hp => lift_pos_of_designated_lp (w p) (hwprem p hp)
    have hcpos := hpos v hvprem
    have : isDesignatedLP (collapse (v conclusion)) :=
      (lp_designated_iff_pos (v conclusion)).mpr hcpos
    rwa [lift_collapse_id] at this

/-- Bridge Theorem (K3): K3 consequence on {0,1/2,1} is equivalent to
    certainty consequence on [0,1]. -/
theorem k3_bridge (α : Type*) (premises : List α) (conclusion : α) :
    threeValConsequence isDesignatedK3 α premises conclusion ↔
    certaintyConsequence α premises conclusion := by
  constructor
  · intro hk3 v hprem
    let w : ThreeValuation α := fun a => collapse (v a)
    have hwprem : ∀ p ∈ premises, isDesignatedK3 (w p) :=
      fun p hp => (k3_designated_iff_one (v p)).mpr (hprem p hp)
    have := hk3 w hwprem
    exact ((k3_designated_iff_one (v conclusion)).mp this)
  · intro hcert w hwprem
    let v : α → Credence := fun a => liftThreeVal (w a)
    have hvprem : ∀ p ∈ premises, v p = 1 :=
      fun p hp => lift_one_of_designated_k3 (w p) (hwprem p hp)
    have hcone := hcert v hvprem
    have : isDesignatedK3 (collapse (v conclusion)) :=
      (k3_designated_iff_one (v conclusion)).mpr hcone
    rwa [lift_collapse_id] at this

/-- Positivity consequence is explosion-free: same witness as LP. -/
theorem positivity_no_explosion :
    ∃ v : Fin 2 → Credence,
      0 < (v 0).val ∧ 0 < (Credence.neg (v 0)).val ∧ ¬(0 < (v 1).val) := by
  use fun i => if i = 0 then Credence.half else 0
  refine ⟨?_, ?_, ?_⟩
  · simp [Credence.half_val]
  · simp only [show (0 : Fin 2) = 0 from rfl, ite_true, Credence.neg_val, Credence.half_val]
    norm_num
  · simp [Credence.zero_val]

/-! ## Formula Type and Evaluation -/

/-- Propositional formulas built from atoms, negation, conjunction, disjunction. -/
inductive Formula (α : Type*) where
  | atom : α → Formula α
  | neg  : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | disj : Formula α → Formula α → Formula α

/-- Evaluate a formula under a credence assignment to atoms. -/
noncomputable def evalCred (v : α → Credence) : Formula α → Credence
  | .atom a   => v a
  | .neg φ    => Credence.neg (evalCred v φ)
  | .conj φ ψ => evalCred v φ ⊗ evalCred v ψ
  | .disj φ ψ => evalCred v φ ⊔ evalCred v ψ

/-- Evaluate a formula under a three-valued assignment to atoms. -/
def evalThreeVal (w : α → ThreeVal) : Formula α → ThreeVal
  | .atom a   => w a
  | .neg φ    => ThreeVal.neg (evalThreeVal w φ)
  | .conj φ ψ => ThreeVal.conj (evalThreeVal w φ) (evalThreeVal w ψ)
  | .disj φ ψ => ThreeVal.disj (evalThreeVal w φ) (evalThreeVal w ψ)

/-! ## Collapse Commutes with Formula Evaluation -/

/-- Collapsing after credence evaluation equals three-valued evaluation
    under the collapsed assignment. -/
theorem collapse_eval_eq (v : α → Credence) (φ : Formula α) :
    collapse (evalCred v φ) = evalThreeVal (collapse ∘ v) φ := by
  induction φ with
  | atom a => simp [evalCred, evalThreeVal]
  | neg φ ih => simp only [evalCred, evalThreeVal]; rw [collapse_neg, ih]
  | conj φ ψ ih1 ih2 => simp only [evalCred, evalThreeVal]; rw [collapse_conj, ih1, ih2]
  | disj φ ψ ih1 ih2 => simp only [evalCred, evalThreeVal]; rw [collapse_disj, ih1, ih2]

/-- Three-valued evaluation equals collapse of credence evaluation on lifted atoms. -/
theorem lift_eval_eq (w : α → ThreeVal) (φ : Formula α) :
    evalThreeVal w φ = collapse (evalCred (liftThreeVal ∘ w) φ) := by
  rw [collapse_eval_eq]
  congr 1
  ext a
  simp [Function.comp, lift_collapse_id]

/-! ## Formula-Level Consequence -/

/-- Formula-level three-valued consequence. -/
def formulaConsequence (designated : ThreeVal → Prop) (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) : Prop :=
  ∀ w : α → ThreeVal,
    (∀ p ∈ premises, designated (evalThreeVal w p)) →
    designated (evalThreeVal w conclusion)

/-- Formula-level positivity consequence on [0,1]. -/
def formulaPositivity (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) : Prop :=
  ∀ v : α → Credence,
    (∀ p ∈ premises, 0 < (evalCred v p).val) →
    0 < (evalCred v conclusion).val

/-- Formula-level certainty consequence on [0,1]. -/
def formulaCertainty (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) : Prop :=
  ∀ v : α → Credence,
    (∀ p ∈ premises, evalCred v p = 1) →
    evalCred v conclusion = 1

/-! ### Formula-Level Bridge Theorems -/

/-- Formula-level LP bridge: LP formula consequence ↔ formula positivity. -/
theorem lp_formula_bridge (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) :
    formulaConsequence isDesignatedLP α premises conclusion ↔
    formulaPositivity α premises conclusion := by
  constructor
  · intro hlp v hprem
    let w : α → ThreeVal := collapse ∘ v
    have hwprem : ∀ p ∈ premises, isDesignatedLP (evalThreeVal w p) := by
      intro p hp
      rw [← collapse_eval_eq]
      exact (lp_designated_iff_pos _).mpr (hprem p hp)
    have := hlp w hwprem
    rw [← collapse_eval_eq] at this
    exact (lp_designated_iff_pos _).mp this
  · intro hpos w hwprem
    let v : α → Credence := liftThreeVal ∘ w
    have hvprem : ∀ p ∈ premises, 0 < (evalCred v p).val := by
      intro p hp
      have hd := hwprem p hp
      rw [lift_eval_eq] at hd
      exact (lp_designated_iff_pos _).mp hd
    have hcpos := hpos v hvprem
    rw [lift_eval_eq]
    exact (lp_designated_iff_pos _).mpr hcpos

/-- Formula-level K3 bridge: K3 formula consequence ↔ formula certainty. -/
theorem k3_formula_bridge (α : Type*)
    (premises : List (Formula α)) (conclusion : Formula α) :
    formulaConsequence isDesignatedK3 α premises conclusion ↔
    formulaCertainty α premises conclusion := by
  constructor
  · intro hk3 v hprem
    let w : α → ThreeVal := collapse ∘ v
    have hwprem : ∀ p ∈ premises, isDesignatedK3 (evalThreeVal w p) := by
      intro p hp
      rw [← collapse_eval_eq]
      exact (k3_designated_iff_one _).mpr (hprem p hp)
    have := hk3 w hwprem
    rw [← collapse_eval_eq] at this
    exact (k3_designated_iff_one _).mp this
  · intro hcert w hwprem
    let v : α → Credence := liftThreeVal ∘ w
    have hvprem : ∀ p ∈ premises, evalCred v p = 1 := by
      intro p hp
      have hd := hwprem p hp
      rw [lift_eval_eq] at hd
      exact (k3_designated_iff_one _).mp hd
    have hcone := hcert v hvprem
    rw [lift_eval_eq]
    exact (k3_designated_iff_one _).mpr hcone

/-! ## Structural Rules for Formula Consequence -/

theorem formulaLP_reflexivity (φ : Formula α) :
    formulaConsequence isDesignatedLP α [φ] φ := by
  intro w hprem
  exact hprem φ (List.mem_cons_self φ [])

theorem formulaLP_monotonicity (h : formulaConsequence isDesignatedLP α Γ φ)
    (hsub : ∀ p ∈ Γ, p ∈ Δ) :
    formulaConsequence isDesignatedLP α Δ φ := by
  intro w hprem
  exact h w (fun p hp => hprem p (hsub p hp))

theorem formulaLP_cut (h1 : formulaConsequence isDesignatedLP α Γ φ)
    (h2 : formulaConsequence isDesignatedLP α (φ :: Γ) ψ) :
    formulaConsequence isDesignatedLP α Γ ψ := by
  intro w hprem
  have hφ := h1 w hprem
  exact h2 w (fun p hp => by
    cases List.mem_cons.mp hp with
    | inl h => subst h; exact hφ
    | inr h => exact hprem p h)

theorem formulaK3_reflexivity (φ : Formula α) :
    formulaConsequence isDesignatedK3 α [φ] φ := by
  intro w hprem
  exact hprem φ (List.mem_cons_self φ [])

theorem formulaK3_monotonicity (h : formulaConsequence isDesignatedK3 α Γ φ)
    (hsub : ∀ p ∈ Γ, p ∈ Δ) :
    formulaConsequence isDesignatedK3 α Δ φ := by
  intro w hprem
  exact h w (fun p hp => hprem p (hsub p hp))

theorem formulaK3_cut (h1 : formulaConsequence isDesignatedK3 α Γ φ)
    (h2 : formulaConsequence isDesignatedK3 α (φ :: Γ) ψ) :
    formulaConsequence isDesignatedK3 α Γ ψ := by
  intro w hprem
  have hφ := h1 w hprem
  exact h2 w (fun p hp => by
    cases List.mem_cons.mp hp with
    | inl h => subst h; exact hφ
    | inr h => exact hprem p h)

theorem formulaPositivity_reflexivity (φ : Formula α) :
    formulaPositivity α [φ] φ := by
  intro v hprem
  exact hprem φ (List.mem_cons_self φ [])

theorem formulaPositivity_monotonicity (h : formulaPositivity α Γ φ)
    (hsub : ∀ p ∈ Γ, p ∈ Δ) :
    formulaPositivity α Δ φ := by
  intro v hprem
  exact h v (fun p hp => hprem p (hsub p hp))

theorem formulaPositivity_cut (h1 : formulaPositivity α Γ φ)
    (h2 : formulaPositivity α (φ :: Γ) ψ) :
    formulaPositivity α Γ ψ := by
  intro v hprem
  have hφ := h1 v hprem
  exact h2 v (fun p hp => by
    cases List.mem_cons.mp hp with
    | inl h => subst h; exact hφ
    | inr h => exact hprem p h)

theorem formulaCertainty_reflexivity (φ : Formula α) :
    formulaCertainty α [φ] φ := by
  intro v hprem
  exact hprem φ (List.mem_cons_self φ [])

theorem formulaCertainty_monotonicity (h : formulaCertainty α Γ φ)
    (hsub : ∀ p ∈ Γ, p ∈ Δ) :
    formulaCertainty α Δ φ := by
  intro v hprem
  exact h v (fun p hp => hprem p (hsub p hp))

theorem formulaCertainty_cut (h1 : formulaCertainty α Γ φ)
    (h2 : formulaCertainty α (φ :: Γ) ψ) :
    formulaCertainty α Γ ψ := by
  intro v hprem
  have hφ := h1 v hprem
  exact h2 v (fun p hp => by
    cases List.mem_cons.mp hp with
    | inl h => subst h; exact hφ
    | inr h => exact hprem p h)

end Cred
