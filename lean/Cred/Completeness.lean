/-
  Cred Completeness: Labelled Consequence is Complete for Semantic Validity

  Soundness (`Cred.derivation_sound_*` in `Sequent.lean`) sends every labelled
  derivation to a semantic consequence.  This module proves the converse for the
  threshold, certainty, and positivity fragments: every semantically valid
  consequence over a list of premises has a labelled derivation in the matching
  formula context.  The two directions combine into completeness equivalences.

  Scope of the result.  The labelled calculus admits each sound consequence
  relation as a one-step rule (`thresholdRule`, `certaintyRule`,
  `positivityRule`).  Completeness therefore holds for the calculus exactly as
  defined: a valid consequence is derivable in one rule application over its
  premise hypotheses.  This is genuine completeness for *this* proof layer.  It
  is not a cut-elimination or normal-form result, and it does not reduce
  validity to the primitive structural and chain-rule fragment alone; the
  `obstruction` section below states precisely what is and is not claimed.
-/

import Cred.Sequent

namespace Cred

variable {α : Type*}

/-! ## Premise Hypotheses

Each premise in a `formulaContext` is available as a labelled hypothesis. -/

theorem hyp_of_mem_threshold (t : Credence) {premises : List (Formula α)}
    {p : Formula α} (hp : p ∈ premises) :
    Derivation (formulaContext (.threshold t) premises)
      { kind := .threshold t, formula := p } :=
  Derivation.hyp (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem hyp_of_mem_certain {premises : List (Formula α)}
    {p : Formula α} (hp : p ∈ premises) :
    Derivation (formulaContext .certain premises)
      { kind := .certain, formula := p } :=
  Derivation.hyp (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem hyp_of_mem_positive {premises : List (Formula α)}
    {p : Formula α} (hp : p ∈ premises) :
    Derivation (formulaContext .positive premises)
      { kind := .positive, formula := p } :=
  Derivation.hyp (List.mem_map.mpr ⟨p, hp, rfl⟩)

/-! ## Completeness -/

/-- Threshold completeness: a valid threshold consequence is derivable in the
    threshold context built from its premises. -/
theorem thresholdConsequence_complete (t : Credence)
    {premises : List (Formula α)} {conclusion : Formula α}
    (h : thresholdConsequence t α premises conclusion) :
    Derivation (formulaContext (.threshold t) premises)
      { kind := .threshold t, formula := conclusion } :=
  Derivation.thresholdRule h (fun _p hp => hyp_of_mem_threshold t hp)

/-- Certainty completeness. -/
theorem formulaCertainty_complete
    {premises : List (Formula α)} {conclusion : Formula α}
    (h : formulaCertainty α premises conclusion) :
    Derivation (formulaContext .certain premises)
      { kind := .certain, formula := conclusion } :=
  Derivation.certaintyRule h (fun _p hp => hyp_of_mem_certain hp)

/-- Positivity completeness. -/
theorem formulaPositivity_complete
    {premises : List (Formula α)} {conclusion : Formula α}
    (h : formulaPositivity α premises conclusion) :
    Derivation (formulaContext .positive premises)
      { kind := .positive, formula := conclusion } :=
  Derivation.positivityRule h (fun _p hp => hyp_of_mem_positive hp)

/-! ## Soundness-Completeness Equivalences

Derivability in the premise-generated context coincides exactly with semantic
validity. -/

theorem thresholdConsequence_iff_derivation (t : Credence)
    {premises : List (Formula α)} {conclusion : Formula α} :
    thresholdConsequence t α premises conclusion ↔
    Derivation (formulaContext (.threshold t) premises)
      { kind := .threshold t, formula := conclusion } :=
  ⟨thresholdConsequence_complete t, derivation_sound_thresholdConsequence⟩

theorem formulaCertainty_iff_derivation
    {premises : List (Formula α)} {conclusion : Formula α} :
    formulaCertainty α premises conclusion ↔
    Derivation (formulaContext .certain premises)
      { kind := .certain, formula := conclusion } :=
  ⟨formulaCertainty_complete, derivation_sound_formulaCertainty⟩

theorem formulaPositivity_iff_derivation
    {premises : List (Formula α)} {conclusion : Formula α} :
    formulaPositivity α premises conclusion ↔
    Derivation (formulaContext .positive premises)
      { kind := .positive, formula := conclusion } :=
  ⟨formulaPositivity_complete, derivation_sound_formulaPositivity⟩

/-! ## Obstruction: No Ex-Falso Survives Completeness

Completeness does not import explosion.  The semantic relation has no ex-falso,
so neither does the derivability it characterizes.  Concretely, `A` and `~A`
positive do not entail an unrelated atom, and the equivalence transports this
gap to the proof layer: there is no valid positivity consequence, hence no
derivation, from {A, ~A} to a disjoint atom.  This is the precise sense in which
the calculus is complete *for a paraconsistent semantics* rather than for
classical validity. -/

theorem positivity_ex_falso_fails :
    ¬ formulaPositivity (Fin 2)
        [Formula.atom 0, Formula.neg (Formula.atom 0)] (Formula.atom 1) := by
  intro h
  have hconcl := h (fun i : Fin 2 => if i = 0 then Credence.half else 0) ?_
  · simp [evalCred, Credence.zero_val] at hconcl
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [evalCred, Credence.half_val]
    · rcases List.mem_cons.mp hp with rfl | hp
      · simp only [evalCred, show (0 : Fin 2) = 0 from rfl, ite_true,
          Credence.neg_val, Credence.half_val]
        norm_num
      · cases hp

/-- The obstruction stated through the completeness equivalence: no labelled
    derivation reaches the unrelated atom, recovered purely from the semantic
    failure of ex-falso without re-running the derivation induction. -/
theorem no_ex_falso_via_completeness :
    ¬ Derivation
        (formulaContext (α := Fin 2) .positive
          [Formula.atom 0, Formula.neg (Formula.atom 0)])
        { kind := .positive, formula := Formula.atom 1 } := by
  rw [← formulaPositivity_iff_derivation]
  exact positivity_ex_falso_fails

end Cred
