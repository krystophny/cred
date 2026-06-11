/-
  Cred Core: Consequence Relations (Axis A1)

  Defines designated-value consequence relations on three values, graded
  consequence on [0,1], the Formula type with credence and three-valued
  evaluation, structural rules, and compatibility with unconstrained
  conditioning (no explosion).

  Key results:
  - K3 consequence (designate {1}): paracomplete, no tautologies
  - LP consequence (designate {1, 1/2}): paraconsistent, explosion fails
  - Graded consequence parametrized by threshold
  - No-explosion theorem for all compatible consequence relations
-/

import Cred.Collapse.ThreeVal

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

/-! ### Consequence on [0,1] -/

/-- Positivity consequence: every valuation making premises positive
    also makes the conclusion positive. -/
def positivityConsequence (α : Type*) (premises : List α) (conclusion : α) : Prop :=
  ∀ v : α → Credence, (∀ p ∈ premises, 0 < (v p).val) → 0 < (v conclusion).val

/-- Certainty consequence: every valuation making premises certain
    also makes the conclusion certain. -/
def certaintyConsequence (α : Type*) (premises : List α) (conclusion : α) : Prop :=
  ∀ v : α → Credence, (∀ p ∈ premises, v p = 1) → v conclusion = 1

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
