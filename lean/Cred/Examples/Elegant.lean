/-
  Cred Examples: Elegant Cases

  A showcase of elementary results where the credence treatment is cleaner
  than the classical or the standard fuzzy one.  Every statement is a real
  theorem reusing already-verified machinery; the per-result doc comments say
  why the credence reading is the simpler one.

  No new semantics is introduced here: each result is a one- or two-line
  consequence of lemmas proved elsewhere in the library.
-/

import Cred.Reductio
import Cred.Fixpoint
import Cred.Cond.Admissible

namespace Cred.Examples.Elegant

open Cred Cred.Credence

/-! ## No explosion from a contradiction -/

/-- Why this is cleaner: classical logic answers a contradictory premise pair
    with ex falso quodlibet, deriving every sentence whatsoever.  Here the
    contradiction `A, ~A` at a positive threshold leaves a surviving reductio
    countermodel for an unrelated atom `B`, so `B` is not forced.  The ground
    of entailment is emptiness of the countermodel set, and that set is
    nonempty, so the inference simply fails rather than collapsing. -/
theorem contradiction_does_not_force_unrelated_atom
    (t : Credence) (htpos : 0 < t.val) (ht : t.val ≤ (1 : ℝ) / 2) :
    ¬ thresholdConsequence t (Fin 2) explosionPremises explosionConclusion :=
  (reductio_ground_is_emptiness_not_contradiction t htpos ht).2

/-- Why this is cleaner: the contradiction is genuinely present among the
    premises (both `A` and `~A` sit in `[t,1]` at the witnessing valuation),
    yet no explosion follows.  Classical logic cannot exhibit this separation:
    a satisfied contradiction is, classically, impossible. -/
theorem contradiction_present_yet_no_explosion
    (t : Credence) (htpos : 0 < t.val) (ht : t.val ≤ (1 : ℝ) / 2) :
    (reductioCountermodels t (Fin 2) explosionPremises explosionConclusion).Nonempty ∧
    ¬ thresholdConsequence t (Fin 2) explosionPremises explosionConclusion :=
  reductio_ground_is_emptiness_not_contradiction t htpos ht

/-! ## Self-reference as a solution set -/

/-- Why this is cleaner: the liar `c = ~c` is not a paradox but an equation,
    and its solution set is the single point `1/2`.  Where classical logic has
    no truth value and must escape into hierarchies or gaps, the credence
    reading returns one definite fixed point. -/
theorem liar_solution_set_is_half :
    solutions neg = {half} :=
  solutions_neg_eq_singleton

/-- Why this is cleaner: the unique liar value is the spread-maximizing
    midpoint `1/2`, recovered directly as the only fixed point of negation. -/
theorem liar_value_unique (c : Credence) (h : c ∈ solutions neg) : c = half := by
  rw [solutions_neg_eq_singleton, Set.mem_singleton_iff] at h
  exact h

/-- Why this is cleaner: the truth-teller `c = c` constrains nothing, so its
    solution set is the entire interval `[0,1]`.  The liar (one solution) and
    the truth-teller (all solutions) are distinguished cleanly by the size of
    their solution sets, with neither producing a paradox. -/
theorem truth_teller_solution_set_is_univ :
    solutions (fun c : Credence => c) = Set.univ :=
  solutions_id_eq_univ

/-- Why this is cleaner: the truth-teller's full solution set is exactly the
    zero-evidence conditioning set `Cond 0 0`.  Two superficially different
    underdetermined problems turn out to be the same total set, a coincidence
    invisible to a two-valued or gap-based treatment. -/
theorem truth_teller_is_zero_evidence_shape :
    solutions (fun c : Credence => c) = Cond 0 0 :=
  truth_teller_same_shape_as_zero_evidence

/-! ## Zero-evidence conditioning is total -/

/-- Why this is cleaner: probability leaves `cred(A | B)` undefined when
    `cred(B) = 0` (the `0/0` of Bayes' rule).  With conditioning primitive via
    the chain rule, the admissible set on zero evidence is all of `[0,1]`:
    impossible evidence imposes no constraint instead of producing a gap. -/
theorem zero_evidence_conditioning_is_total :
    Cond 0 0 = Set.univ :=
  cond_zero_zero_univ

/-- Why this is cleaner: every credence is an admissible conditional on zero
    evidence, stated as a membership fact.  No exceptional case, no `0/0`. -/
theorem any_credence_admissible_on_zero_evidence (c : Credence) :
    c ∈ Cond 0 0 := by
  rw [cond_zero_zero_univ]; exact Set.mem_univ c

/-! ## Independence makes evidence irrelevant -/

/-- Why this is cleaner: under independence the joint factors as the product
    `a ⊗ e`, and conditioning on positive evidence `e` returns the prior `a`
    exactly: `Cond (a ⊗ e) e = {a}`.  The chain rule delivers irrelevance of
    independent evidence as a one-line algebraic identity, with no separate
    independence axiom and no division by the evidence. -/
theorem independent_evidence_conditional_is_prior
    (a e : Credence) (he : 0 < e.val) :
    Cond (a ⊗ e) e = {a} := by
  have hle : (a ⊗ e).val ≤ e.val := by
    rw [conj_val]
    calc a.val * e.val ≤ 1 * e.val :=
          mul_le_mul_of_nonneg_right a.le_one e.nonneg
      _ = e.val := one_mul _
  rw [cond_singleton_of_pos (a ⊗ e) e he hle]
  congr 1
  apply Credence.ext
  show (a ⊗ e).val / e.val = a.val
  rw [conj_val, mul_div_assoc, div_self (ne_of_gt he), mul_one]

/-- Why this is cleaner: stated as membership, the prior `a` is an admissible
    conditional credence for the independent product joint `a ⊗ e`.  No appeal
    to a probabilistic independence definition is needed; it is the chain rule
    at the product joint. -/
theorem prior_is_admissible_for_product_joint (a e : Credence) :
    a ∈ Cond (a ⊗ e) e := by
  show a ⊗ e = a ⊗ e
  rfl

end Cred.Examples.Elegant
