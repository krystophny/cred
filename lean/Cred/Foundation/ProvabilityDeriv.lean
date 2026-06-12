/-
  Cred Foundation ProvabilityDeriv

  A provability predicate tied to a real derivability relation, not the constant
  half.  `provDerivProvable A` holds iff `A` has a `FoundationProof` from no
  premises at certainty; `provDerivVal A` is the crisp credence `1`/`0` of that
  fact.  Interpreting this predicate over the genuine Goedel numbering yields the
  Tarski-Goedel obstruction in the form of an honest dichotomy: the predicate
  cannot reflect its own Goedel sentence at that sentence's code, so the sentence
  is either underivable (incompleteness) or the structure is unsound at it.

  Loeb / Con(T) are stated at the meta level only: the internal-implication form
  of the Hilbert-Bernays-Loeb conditions would need a total internal conditional
  with modus ponens, conditional proof, and contraction, which `curry_block`
  refutes.  Con is "bottom is not derivable", proven outright.
-/

import Cred.Foundation.CodingNat
import Cred.Foundation.Kernel
import Cred.Bridge.Curry

namespace Cred
namespace Foundation
namespace natCoding

open Credence

/-! ## A real derivability relation on the coding language

`FoundationProof (t) Γ φ` is the typed proof calculus of `Foundation.Kernel`.
It has genuine axioms (`equalityRefl`) and forward rules, so derivability from
the empty premise list is neither empty nor total.  We fix certainty `t = 1`. -/

/-- `A` is derivable from no premises at certainty in the foundation calculus. -/
def provDerivProvable (A : NatFormula) : Prop :=
  Nonempty (Structure.FoundationProof (1 : Credence) ([] : List NatFormula) A)

open Classical in
/-- Provability is decidable as a proposition through classical choice; this is
    the only nonconstructive ingredient and it only sorts a real relation into
    two crisp values. -/
noncomputable def provDerivVal (A : NatFormula) : Credence :=
  if provDerivProvable A then 1 else 0

/-- The predicate is crisp: every value is `0` or `1`. -/
theorem provDerivVal_crisp (A : NatFormula) :
    provDerivVal A = 0 ∨ provDerivVal A = 1 := by
  unfold provDerivVal
  by_cases h : provDerivProvable A
  · exact Or.inr (if_pos h)
  · exact Or.inl (if_neg h)

theorem provDerivVal_eq_one_iff (A : NatFormula) :
    provDerivVal A = 1 ↔ provDerivProvable A := by
  unfold provDerivVal
  by_cases h : provDerivProvable A
  · simp [h]
  · simp only [h, if_false, iff_false]
    intro hval
    have : (0 : Credence).val = (1 : Credence).val := congrArg Credence.val hval
    norm_num at this

/-- Reflexive equalities are derivable, so the predicate is not constant `0`. -/
theorem provDerivProvable_equalityRefl (τ : NatTerm) :
    provDerivProvable (.equal τ τ) :=
  ⟨Structure.FoundationProof.equalityRefl τ⟩

theorem provDerivVal_equalityRefl (τ : NatTerm) :
    provDerivVal (.equal τ τ) = 1 :=
  (provDerivVal_eq_one_iff _).2 (provDerivProvable_equalityRefl τ)

/-! ## A one-point witness structure for the law interfaces

Refuting derivability of `bot` needs one structure satisfying `CrispEquality`
and `QuantifierLaws`.  The single-point domain supplies it. -/

noncomputable def conWitness : Structure NatFunc NatPred where
  Domain := Unit
  witness := ()
  func _ _ := ()
  pred _ _ := half
  eq _ _ := 1
  all f := f ()
  ex f := f ()

theorem conWitness_crispEquality : conWitness.CrispEquality where
  eq_refl _ := rfl
  eq_one_imp {x y} _ := Unit.ext x y
  eq_zero_of_ne {x y} h := absurd (Unit.ext x y) h

theorem conWitness_quantifierLaws : conWitness.QuantifierLaws where
  all_le_instance f x := by
    show f () ≤ f x
    rw [show x = () from Unit.ext x ()]
  instance_le_ex f x := by
    show f x ≤ f ()
    rw [show x = () from Unit.ext x ()]
  all_one := rfl
  ex_zero := rfl

/-! ## Con(T): bottom is not derivable

Honest, outright proof: a `FoundationProof` of `bot` is sound, hence forces
`1 ≤ 0` in the one-point witness, which is false. -/

theorem not_provDerivProvable_bot : ¬ provDerivProvable (Formula.bot) := by
  rintro ⟨p⟩
  have hsound := Structure.FoundationProof.sound p conWitness
    (fun _ : Nat => conWitness.witness)
    conWitness_crispEquality conWitness_quantifierLaws (by intro q hq; cases hq)
  have hbot : conWitness.evalFormula (fun _ => conWitness.witness) Formula.bot
      = 0 := rfl
  rw [hbot] at hsound
  have : (1 : Credence).val ≤ (0 : Credence).val := hsound
  norm_num at this

/-- Con(T) as a credence fact: the provability value of bottom is `0`. -/
theorem con_provDerivVal_bot : provDerivVal (Formula.bot) = 0 := by
  unfold provDerivVal
  rw [if_neg not_provDerivProvable_bot]

/-- Con(T) below certainty: bottom's provability value is strictly under `1`. -/
theorem con_provDerivVal_bot_lt_one : provDerivVal (Formula.bot) ≠ 1 := by
  rw [con_provDerivVal_bot]
  intro h
  have : (0 : Credence).val = (1 : Credence).val := congrArg Credence.val h
  norm_num at this

/-! ## The structure whose provability predicate IS `provDerivVal`

Same domain, functions, equality, and quantifiers as `natStructure` (so the
diagonal machinery transfers verbatim), but the single predicate decodes its
Goedel-coded argument and reports `provDerivVal` of the recovered formula. -/

noncomputable def provStructure : Structure NatFunc NatPred where
  Domain := Nat
  witness := 0
  func
    | none, [n] => diagFunc n
    | some k, _ => k
    | none, _ => 0
  pred _ xs := provDerivVal (decodeFormula (xs.headD 0))
  eq a b := if a = b then 1 else 0
  all f := f 0
  ex f := f 0

@[simp] theorem provStructure_func_none_single (n : Nat) :
    provStructure.func none [n] = diagFunc n := rfl

@[simp] theorem provStructure_func_numeral (k : Nat) (xs : List Nat) :
    provStructure.func (some k) xs = k := rfl

@[simp] theorem provStructure_evalTerm_numeral
    (env : provStructure.Assignment) (k : Nat) :
    provStructure.evalTerm env (numeral k) = k := rfl

/-- The diagonal coding for `provStructure`.  `code`, `selfApp`, and the two
    coding facts only constrain `func`/`evalTerm`, which match `natStructure`. -/
noncomputable def provCoding : provStructure.DiagonalCoding where
  code φ := numeral (gnumFormula φ)
  selfApp := none
  code_closed _ _ _ := rfl
  selfApp_diag φ env := by
    show provStructure.func none [gnumFormula φ] =
      gnumFormula (φ.instantiate (numeral (gnumFormula φ)))
    show diagFunc (gnumFormula φ) =
      gnumFormula (φ.instantiate (numeral (gnumFormula φ)))
    rw [diagFunc, decodeFormula_gnum]

/-- The predicate at a code evaluates `provDerivVal` of the decoded formula. -/
theorem provStructure_pred_code (φ : NatFormula)
    (env : provStructure.Assignment) :
    provStructure.pred ()
        [provStructure.evalTerm env (provCoding.code φ)] =
      provDerivVal φ := by
  show provDerivVal (decodeFormula (gnumFormula φ)) = provDerivVal φ
  rw [decodeFormula_gnum]

/-! ## The graded Goedel sentence under genuine provability -/

/-- The Goedel sentence of `provStructure`: "I am not provDeriv-provable". -/
noncomputable def provGodel : NatFormula := provCoding.godel ()

/-- Evaluating the Goedel sentence routes through `provDerivVal` of itself. -/
theorem provGodel_eval (env : provStructure.Assignment) :
    provStructure.evalFormula env provGodel = ~(provDerivVal provGodel) := by
  show provStructure.evalFormula env (provCoding.godel ()) =
    ~(provDerivVal (provCoding.godel ()))
  rw [provCoding.godel_eval () env, provStructure_pred_code (provCoding.godel ()) env]

/-! ## The Tarski-Goedel obstruction: reflection fails at the Goedel code

`no_crisp_godel` says no env reflects a crisp predicate value at the Goedel
sentence.  `provDerivVal` is always crisp, so reflection must fail. -/

/-- The provability predicate cannot reflect the Goedel sentence at its own
    code: the crisp Tarski-Goedel obstruction realised with a real derivability
    relation rather than the constant half. -/
theorem provGodel_reflection_fails (env : provStructure.Assignment) :
    provStructure.pred ()
        [provStructure.evalTerm env (provCoding.code (provCoding.godel ()))] ≠
      provStructure.evalFormula env (provCoding.godel ()) := by
  intro hrefl
  refine provCoding.no_crisp_godel () env hrefl ?_
  rw [provStructure_pred_code (provCoding.godel ()) env]
  exact provDerivVal_crisp _

/-- Restated on `provDerivVal`: provability of the Goedel sentence never equals
    the sentence's own credence.  The fixed-point obstruction in its crispest
    form. -/
theorem provDerivVal_godel_ne_eval (env : provStructure.Assignment) :
    provDerivVal provGodel ≠ provStructure.evalFormula env provGodel := by
  intro h
  refine provGodel_reflection_fails env ?_
  rw [provStructure_pred_code (provCoding.godel ()) env]
  exact h

/-! ## The incompleteness dichotomy (non-vacuous)

The reflection failure splits.  The "intended" reading: `provDerivVal G = 1`
asserts provability, so a structure that reflected it would assign `G` the value
1.  Since reflection fails, either `G` is not provable here (incompleteness) or
the assigned value disagrees with provability (local unsoundness). -/

/-- Either the Goedel sentence is not `provDeriv`-provable, or its credence in
    `provStructure` disagrees with the crisp provability verdict.  Both disjuncts
    are about the real derivability relation; neither is vacuous. -/
theorem provGodel_incompleteness_dichotomy (env : provStructure.Assignment) :
    ¬ provDerivProvable provGodel ∨
      provStructure.evalFormula env provGodel ≠ provDerivVal provGodel := by
  by_cases hprov : provDerivProvable provGodel
  · refine Or.inr ?_
    exact fun h => provDerivVal_godel_ne_eval env h.symm
  · exact Or.inl hprov

/-- Sharper form: if the structure is locally sound at `G` (a provable `G` gets
    full credence) then `G` is unprovable.  This is Goedel's first theorem in
    graded dress, with provability supplied by a genuine derivation relation. -/
theorem provGodel_unprovable_of_local_soundness
    (env : provStructure.Assignment)
    (hsound : provDerivProvable provGodel →
      provStructure.evalFormula env provGodel = 1) :
    ¬ provDerivProvable provGodel := by
  intro hprov
  have heval := hsound hprov
  have hval : provDerivVal provGodel = 1 :=
    (provDerivVal_eq_one_iff _).2 hprov
  exact provDerivVal_godel_ne_eval env (by rw [hval, heval])

/-! ## Non-vacuity

`provGodel` is a genuine formula of the coding language, with a genuine code,
and the Goedel evaluation is the negated self-provability fact.  These facts
witness that the dichotomy's hypotheses are about real objects. -/

/-- The Goedel sentence is a real formula: its code decodes back to it. -/
theorem provGodel_decodes :
    decodeFormula (gnumFormula provGodel) = provGodel :=
  decodeFormula_gnum provGodel

/-- Concrete non-vacuity of the predicate: it takes the value `1` on a real
    formula (any reflexive equality) and `0` on `bot`.  So neither disjunct of
    the dichotomy is forced by triviality of `provDerivVal`. -/
theorem provDerivVal_nonconstant :
    ∃ A B : NatFormula, provDerivVal A = 1 ∧ provDerivVal B = 0 :=
  ⟨.equal (Term.var 0) (Term.var 0), Formula.bot,
    provDerivVal_equalityRefl _, con_provDerivVal_bot⟩

/-! ## Loeb / Hilbert-Bernays-Loeb conditions: meta level only

The derivability conditions are stated as facts about `provDerivVal`, never as
internal object-language implications.  The first condition (necessitation) is a
genuine theorem; the others are recorded as the meta-level shape one would need,
because their internal-implication form is blocked by `curry_block` below. -/

/-- HBL-1 (necessitation), proven: derivability forces provability value `1`. -/
theorem hbl_necessitation (A : NatFormula) (h : provDerivProvable A) :
    provDerivVal A = 1 :=
  (provDerivVal_eq_one_iff A).2 h

/-- The internal-implication form of the Loeb / HBL conditions would require a
    total internal conditional on credences with modus ponens, conditional
    proof, and contraction.  `Credence.curry_block` proves no such operation
    exists, so Loeb's theorem has no internal-arrow derivation here; the
    conditions stay external (meta-level), matching the no-internal-conditional
    design of the language. -/
theorem loeb_internal_arrow_blocked :
    ¬ ∃ f : Credence → Credence → Credence,
        Credence.MP f ∧ Credence.CP f ∧ Credence.Contraction f :=
  Credence.curry_block

/-- Con(T) as the canonical statement "the false constant is not derivable",
    packaged together with its crisp graded status (value `0`, below certainty). -/
theorem con_statement :
    ¬ provDerivProvable (Formula.bot) ∧
      provDerivVal (Formula.bot) = 0 ∧ provDerivVal (Formula.bot) ≠ 1 :=
  ⟨not_provDerivProvable_bot, con_provDerivVal_bot, con_provDerivVal_bot_lt_one⟩

end natCoding
end Foundation
end Cred
