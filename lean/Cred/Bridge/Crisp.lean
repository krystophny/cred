/-
  Cred Bridge: Crisp Embedding

  Classical logic is the {0,1} fragment of Cred. The embedding Bool → Credence
  is a homomorphism for negation, conjunction, and disjunction; formula
  evaluation commutes with it (crisp_eval_eq); classical validity coincides
  with credence-validity over crisp valuations (crisp_embedding); and on crisp
  valuations the classical, positivity, and certainty consequence relations
  coincide (crisp_certainty_iff_classical, crisp_positivity_iff_classical).

  Conditioning marks the exact boundary of this conservativity. On crisp
  values the admissible set Cond (embed j) (embed e) is the singleton of the
  material conditional exactly when the evidence e is true
  (material_divergence). At empty antecedent (e = 0, j = 0) classical logic
  assigns vacuous truth; Cred admits every credence, the classical value
  among them (vacuous_truth_admissible, cond_underdetermined_iff).

  The final section turns the crisp survivors from the proof-pattern
  inventory into theorems: case analysis on the three regions of [0,1],
  formula-level double negation elimination, crisp excluded middle and
  non-contradiction, and certainty of classical tautologies.

  Naming: the classical evaluator is called classicalEval, not Classical.eval,
  to avoid Lean's Classical namespace.
-/

import Cred.Core.Consequence
import Cred.Cond.Admissible

namespace Cred

variable {α : Type*}

/-! ## The Embedding -/

/-- 0 and 1 as Credence are distinct. -/
theorem credence_zero_ne_one : (0 : Credence) ≠ 1 := by
  intro h
  have hval : (0 : Credence).val = (1 : Credence).val := congrArg Credence.val h
  simp only [Credence.zero_val, Credence.one_val] at hval
  norm_num at hval

/-- Embed the Booleans into the credence values: false ↦ 0, true ↦ 1. -/
def embed : Bool → Credence
  | false => 0
  | true  => 1

@[simp] theorem embed_false : embed false = 0 := rfl
@[simp] theorem embed_true : embed true = 1 := rfl

/-- Embedded values are crisp. -/
theorem embed_crisp (b : Bool) : embed b = 0 ∨ embed b = 1 := by
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The embedding reflects truth: embed b = 1 iff b is true. -/
theorem embed_eq_one_iff (b : Bool) : embed b = 1 ↔ b = true := by
  cases b
  · constructor
    · intro h
      exact absurd h credence_zero_ne_one
    · intro h
      simp at h
  · simp

/-- The embedding is a negation homomorphism. -/
theorem embed_neg (b : Bool) : ~(embed b) = embed (!b) := by
  cases b <;> simp

/-- The embedding is a conjunction homomorphism. -/
theorem embed_conj (b₁ b₂ : Bool) : embed b₁ ⊗ embed b₂ = embed (b₁ && b₂) := by
  cases b₁ <;> cases b₂ <;> simp

/-- The embedding is a disjunction homomorphism. -/
theorem embed_disj (b₁ b₂ : Bool) : embed b₁ ⊔ embed b₂ = embed (b₁ || b₂) := by
  cases b₁ <;> cases b₂ <;> simp

/-- Every crisp valuation factors through the embedding. -/
theorem crisp_exists_bool (w : α → Credence) (hw : ∀ a, w a = 0 ∨ w a = 1) :
    ∃ v : α → Bool, w = fun a => embed (v a) := by
  classical
  refine ⟨fun a => if w a = 1 then true else false, funext fun a => ?_⟩
  rcases hw a with h | h
  · change w a = embed (if w a = 1 then true else false)
    have hne : w a ≠ 1 := by rw [h]; exact credence_zero_ne_one
    rw [if_neg hne, embed_false, h]
  · change w a = embed (if w a = 1 then true else false)
    rw [if_pos h, embed_true, h]

/-! ## Classical Evaluation -/

/-- Two-valued classical evaluation of a formula under a Boolean valuation. -/
def classicalEval (v : α → Bool) : Formula α → Bool
  | .atom a   => v a
  | .neg φ    => !(classicalEval v φ)
  | .conj φ ψ => classicalEval v φ && classicalEval v ψ
  | .disj φ ψ => classicalEval v φ || classicalEval v ψ

/-- Credence evaluation on embedded valuations commutes with classical
    evaluation through the embedding. -/
theorem crisp_eval_eq (v : α → Bool) (φ : Formula α) :
    evalCred (fun a => embed (v a)) φ = embed (classicalEval v φ) := by
  induction φ with
  | atom a => rfl
  | neg φ ih => simp only [evalCred, classicalEval, ih, embed_neg]
  | conj φ ψ ihφ ihψ => simp only [evalCred, classicalEval, ihφ, ihψ, embed_conj]
  | disj φ ψ ihφ ihψ => simp only [evalCred, classicalEval, ihφ, ihψ, embed_disj]

/-- Credence evaluation preserves crispness. -/
theorem evalCred_crisp (w : α → Credence) (hw : ∀ a, w a = 0 ∨ w a = 1)
    (φ : Formula α) : evalCred w φ = 0 ∨ evalCred w φ = 1 := by
  obtain ⟨v, rfl⟩ := crisp_exists_bool w hw
  rw [crisp_eval_eq]
  exact embed_crisp _

/-- Crisp embedding: classical validity coincides with credence-validity
    over crisp valuations. Nothing classical is lost. -/
theorem crisp_embedding (φ : Formula α) :
    (∀ v : α → Bool, classicalEval v φ = true) ↔
    (∀ w : α → Credence, (∀ a, w a = 0 ∨ w a = 1) → evalCred w φ = 1) := by
  constructor
  · intro h w hw
    obtain ⟨v, rfl⟩ := crisp_exists_bool w hw
    rw [crisp_eval_eq, h v, embed_true]
  · intro h v
    have hone := h (fun a => embed (v a)) (fun a => embed_crisp (v a))
    rw [crisp_eval_eq] at hone
    exact (embed_eq_one_iff _).mp hone

/-! ## Consequence Coincidence on Crisp Valuations -/

/-- Classical consequence: Boolean valuations making all premises true make
    the conclusion true. -/
def classicalConsequence (α : Type*) (premises : List (Formula α))
    (conclusion : Formula α) : Prop :=
  ∀ v : α → Bool, (∀ p ∈ premises, classicalEval v p = true) →
    classicalEval v conclusion = true

/-- Certainty consequence restricted to crisp valuations. -/
def crispCertainty (α : Type*) (premises : List (Formula α))
    (conclusion : Formula α) : Prop :=
  ∀ w : α → Credence, (∀ a, w a = 0 ∨ w a = 1) →
    (∀ p ∈ premises, evalCred w p = 1) → evalCred w conclusion = 1

/-- Positivity consequence restricted to crisp valuations. -/
def crispPositivity (α : Type*) (premises : List (Formula α))
    (conclusion : Formula α) : Prop :=
  ∀ w : α → Credence, (∀ a, w a = 0 ∨ w a = 1) →
    (∀ p ∈ premises, 0 < (evalCred w p).val) → 0 < (evalCred w conclusion).val

/-- On crisp values, positivity and certainty agree: 0 < c.val iff c = 1. -/
theorem crisp_pos_iff_one (c : Credence) (h : c = 0 ∨ c = 1) :
    0 < c.val ↔ c = 1 := by
  rcases h with rfl | rfl
  · simp only [Credence.zero_val, lt_self_iff_false, false_iff]
    exact credence_zero_ne_one
  · simp only [Credence.one_val, zero_lt_one, true_iff]

/-- The global certainty consequence restricts to crisp certainty. -/
theorem formulaCertainty_implies_crisp (α : Type*) (premises : List (Formula α))
    (conclusion : Formula α) (h : formulaCertainty α premises conclusion) :
    crispCertainty α premises conclusion :=
  fun w _ hprem => h w hprem

/-- The global positivity consequence restricts to crisp positivity. -/
theorem formulaPositivity_implies_crisp (α : Type*) (premises : List (Formula α))
    (conclusion : Formula α) (h : formulaPositivity α premises conclusion) :
    crispPositivity α premises conclusion :=
  fun w _ hprem => h w hprem

/-- On crisp valuations, certainty consequence is classical consequence. -/
theorem crisp_certainty_iff_classical (α : Type*) (premises : List (Formula α))
    (conclusion : Formula α) :
    crispCertainty α premises conclusion ↔
    classicalConsequence α premises conclusion := by
  constructor
  · intro h v hprem
    have hconcl := h (fun a => embed (v a)) (fun a => embed_crisp (v a))
      (fun p hp => by rw [crisp_eval_eq, hprem p hp, embed_true])
    rw [crisp_eval_eq] at hconcl
    exact (embed_eq_one_iff _).mp hconcl
  · intro h w hw hprem
    obtain ⟨v, rfl⟩ := crisp_exists_bool w hw
    have hclprem : ∀ p ∈ premises, classicalEval v p = true := by
      intro p hp
      have hone := hprem p hp
      rw [crisp_eval_eq] at hone
      exact (embed_eq_one_iff _).mp hone
    rw [crisp_eval_eq, h v hclprem, embed_true]

/-- On crisp valuations, positivity consequence is certainty consequence. -/
theorem crisp_positivity_iff_certainty (α : Type*) (premises : List (Formula α))
    (conclusion : Formula α) :
    crispPositivity α premises conclusion ↔
    crispCertainty α premises conclusion := by
  constructor
  · intro h w hw hprem
    have hpos := h w hw (fun p hp => by simp [hprem p hp])
    exact (crisp_pos_iff_one _ (evalCred_crisp w hw conclusion)).mp hpos
  · intro h w hw hprem
    have hone := h w hw (fun p hp =>
      (crisp_pos_iff_one _ (evalCred_crisp w hw p)).mp (hprem p hp))
    simp [hone]

/-- On crisp valuations, positivity consequence is classical consequence.
    Together with the previous two theorems: classical, positivity, and
    certainty consequence coincide on the crisp fragment. -/
theorem crisp_positivity_iff_classical (α : Type*) (premises : List (Formula α))
    (conclusion : Formula α) :
    crispPositivity α premises conclusion ↔
    classicalConsequence α premises conclusion :=
  (crisp_positivity_iff_certainty α premises conclusion).trans
    (crisp_certainty_iff_classical α premises conclusion)

/-! ## Conditioning on Crisp Values -/

namespace Credence

/-- Certain evidence pins the conditional to the joint: Cond j 1 = {j}. -/
theorem cond_one_singleton (j : Credence) : Cond j 1 = {j} := by
  ext c
  simp only [Cond, Set.mem_setOf_eq, conj_one, Set.mem_singleton_iff]

/-- Impossible evidence with a nonzero joint admits no conditional. -/
theorem cond_zero_empty (j : Credence) (hj : j ≠ 0) : Cond j 0 = ∅ := by
  ext c
  simp only [Cond, Set.mem_setOf_eq, conj_zero, Set.mem_empty_iff_false, iff_false]
  exact fun h => hj h.symm

/-- The crisp conditioning table: certain evidence yields the singleton of
    the joint, the empty antecedent with zero joint yields all of [0,1]
    (cond_zero_zero_univ), and a nonzero joint over impossible evidence
    yields the empty set. -/
theorem crisp_cond_table (j : Credence) :
    Cond j 1 = {j} ∧ Cond 0 0 = Set.univ ∧ (j ≠ 0 → Cond j 0 = ∅) :=
  ⟨cond_one_singleton j, cond_zero_zero_univ, fun hj => cond_zero_empty j hj⟩

end Credence

/-! ## The Divergence Theorem

The material conditional, read off the (joint, evidence) pair: when the
evidence B is true, A ∧ B coincides with A, so the conditional value is the
joint; when B is false, classical logic assigns vacuous truth. Admissible
conditioning reproduces this table exactly when the evidence is true. The
empty-antecedent case is the unique departure: classical logic fills it with
vacuous truth, Cred leaves it underdetermined. -/

/-- The material conditional on the (joint, evidence) pair. -/
def materialCond (j e : Bool) : Bool := !e || j

@[simp] theorem materialCond_true (j : Bool) : materialCond j true = j := by
  cases j <;> rfl

@[simp] theorem materialCond_false (j : Bool) : materialCond j false = true := rfl

/-- Divergence theorem: under coherence (a true joint forces true evidence),
    the admissible set is the singleton of the material conditional exactly
    when the evidence is true. The empty-antecedent case e = false is the
    unique departure from classical logic: the admissible set is all of
    [0,1], not the singleton {1} of vacuous truth. -/
theorem material_divergence (j e : Bool) (hcoh : j = true → e = true) :
    Credence.Cond (embed j) (embed e) = {embed (materialCond j e)} ↔ e = true := by
  constructor
  · intro h
    cases e with
    | true => rfl
    | false =>
      have hj : j = false := by
        cases j
        · rfl
        · exact absurd (hcoh rfl) (by simp)
      subst hj
      rw [embed_false, Credence.cond_zero_zero_univ, materialCond_false,
        embed_true] at h
      have h0 : (0 : Credence) ∈ (Set.univ : Set Credence) := Set.mem_univ 0
      rw [h] at h0
      exfalso
      exact credence_zero_ne_one (Set.mem_singleton_iff.mp h0)
  · intro he
    subst he
    rw [embed_true, materialCond_true]
    exact Credence.cond_one_singleton (embed j)

/-- The classical vacuous-truth value stays admissible at empty antecedent. -/
theorem vacuous_truth_admissible : (1 : Credence) ∈ Credence.Cond 0 0 := by
  rw [Credence.cond_zero_zero_univ]
  exact Set.mem_univ 1

/-- So does every other credence: the empty-antecedent conditional is
    underdetermined, not vacuously true. -/
theorem empty_antecedent_underdetermined (c : Credence) :
    c ∈ Credence.Cond 0 0 := by
  rw [Credence.cond_zero_zero_univ]
  exact Set.mem_univ c

/-- On crisp values, full underdetermination occurs exactly at the empty
    antecedent with coherent joint: the admissible set is all of [0,1] iff
    both joint and evidence are false. -/
theorem cond_underdetermined_iff (j e : Bool) :
    Credence.Cond (embed j) (embed e) = Set.univ ↔ (j = false ∧ e = false) := by
  constructor
  · intro h
    cases e with
    | true =>
      exfalso
      rw [embed_true, Credence.cond_one_singleton] at h
      have h0 : (0 : Credence) ∈ ({embed j} : Set Credence) := by
        rw [h]; exact Set.mem_univ 0
      have h1 : (1 : Credence) ∈ ({embed j} : Set Credence) := by
        rw [h]; exact Set.mem_univ 1
      rw [Set.mem_singleton_iff] at h0 h1
      exact credence_zero_ne_one (h0.trans h1.symm)
    | false =>
      cases j with
      | false => exact ⟨rfl, rfl⟩
      | true =>
        exfalso
        rw [embed_true, embed_false,
          Credence.cond_zero_empty 1 (fun h1 => credence_zero_ne_one h1.symm)] at h
        have h0 : (0 : Credence) ∈ (∅ : Set Credence) := by
          rw [h]; exact Set.mem_univ 0
        exact Set.not_mem_empty 0 h0
  · rintro ⟨rfl, rfl⟩
    rw [embed_false]
    exact Credence.cond_zero_zero_univ

/-! ## Proof-Pattern Inventory

Classical proof patterns surviving crisply, as theorems: case analysis on
the three regions of [0,1], double negation elimination at the formula
level, excluded middle and non-contradiction on the crisp fragment, and
certainty of classical tautologies (the direct-proof pattern). The interior
degradation of excluded middle is certainty_ge_three_quarters, restated
here in ⊔/~ form. -/

/-- Proof by cases on the three regions of [0,1]: a property holding at 0,
    at 1, and on the interior holds everywhere. -/
theorem credence_cases (P : Credence → Prop) (h0 : P 0) (h1 : P 1)
    (hint : ∀ c : Credence, 0 < c.val → c.val < 1 → P c) (c : Credence) :
    P c := by
  rcases lt_or_eq_of_le c.nonneg with hpos | hzero
  · rcases lt_or_eq_of_le c.le_one with hlt | hone
    · exact hint c hpos hlt
    · have hc : c = 1 := by
        ext
        simp only [Credence.one_val]
        exact hone
      rw [hc]
      exact h1
  · have hc : c = 0 := by
      ext
      simp only [Credence.zero_val]
      exact hzero.symm
    rw [hc]
    exact h0

/-- Double negation elimination at the formula level: evaluation of ¬¬φ
    equals evaluation of φ, on every valuation, crisp or not. -/
theorem double_neg_elim_formula (v : α → Credence) (φ : Formula α) :
    evalCred v (Formula.neg (Formula.neg φ)) = evalCred v φ := by
  simp only [evalCred, Credence.neg_neg]

/-- Excluded middle holds crisply: c ⊔ ~c = 1 for c ∈ {0,1}. -/
theorem excluded_middle_crisp (c : Credence) (h : c = 0 ∨ c = 1) :
    c ⊔ ~c = 1 :=
  (Credence.certainty_eq_one_iff c).mpr h

/-- In the interior, excluded middle degrades but never below 3/4
    (restatement of certainty_ge_three_quarters in ⊔/~ form). -/
theorem excluded_middle_lower_bound (c : Credence) :
    (3 : ℝ) / 4 ≤ (c ⊔ ~c).val :=
  Credence.certainty_ge_three_quarters c

/-- Non-contradiction holds crisply: c ⊗ ~c = 0 for c ∈ {0,1}. -/
theorem non_contradiction_crisp (c : Credence) (h : c = 0 ∨ c = 1) :
    c ⊗ ~c = 0 :=
  (Credence.spread_eq_zero_iff c).mpr h

/-- Formula-level excluded middle on crisp valuations: φ ∨ ¬φ is certain. -/
theorem crisp_excluded_middle_formula (w : α → Credence)
    (hw : ∀ a, w a = 0 ∨ w a = 1) (φ : Formula α) :
    evalCred w (Formula.disj φ (Formula.neg φ)) = 1 := by
  have h := evalCred_crisp w hw φ
  simp only [evalCred]
  exact excluded_middle_crisp _ h

/-- Formula-level non-contradiction on crisp valuations: φ ∧ ¬φ is
    impossible. -/
theorem crisp_non_contradiction_formula (w : α → Credence)
    (hw : ∀ a, w a = 0 ∨ w a = 1) (φ : Formula α) :
    evalCred w (Formula.conj φ (Formula.neg φ)) = 0 := by
  have h := evalCred_crisp w hw φ
  simp only [evalCred]
  exact non_contradiction_crisp _ h

/-- Direct-proof pattern: every classical tautology evaluates to certainty
    on crisp valuations (pointwise form of crisp_embedding). -/
theorem classical_tautology_certain (φ : Formula α)
    (h : ∀ v : α → Bool, classicalEval v φ = true)
    (w : α → Credence) (hw : ∀ a, w a = 0 ∨ w a = 1) :
    evalCred w φ = 1 :=
  (crisp_embedding φ).mp h w hw

end Cred
