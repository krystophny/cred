/-
  Cred Foundation: the Sigma-1 layer of arithmetic

  This builds the object-language machinery that the recursion-theoretic
  representability of provability (`Representability.lean`) was missing: a
  definable order on the Robinson Q signature, the quantifier-free and Sigma-1
  formula classes, their crisp evaluation in the standard model, and Sigma-1
  completeness (a true existential has a numeral witness). On top of that it
  states the representability target an object-language provability formula must
  meet, and pins the second-incompleteness boundary to the Curry block: even
  granting such a formula, the internal Loeb arrow has no total carrier, so the
  second incompleteness theorem does not internalize as an object conditional.

  The approach mirrors the classical arithmetization formalized in
  FormalizedFormalLogic/Foundation, transported to Cred's graded (credence)
  semantics where equality is crisp and quantifiers are genuine inf/sup.
-/

import Cred.Foundation.Arithmetic
import Cred.Foundation.Representability
import Cred.Bridge.Curry

namespace Cred
namespace Foundation
namespace arithQ

open Credence

/-! ## A definable order

The Q signature has no order symbol, but `a ≤ b` is definable as `∃ c. a + c = b`.
Under the fresh existential the free variables of `a`, `b` shift up by one, so we
rename them with `Nat.succ` before placing them under the binder. -/

/-- Definable order `a ≤ b := ∃ c, a + c = b`. -/
def leF (a b : ArithQTerm) : ArithQFormula :=
  .existsE (.equal (addT (Term.rename Nat.succ a) (v 0)) (Term.rename Nat.succ b))

-- `natModel.Domain` is definitionally `Nat`, but instance synthesis does not
-- unfold it; expose the order so statements about evaluated terms elaborate.
instance : LE natModel.Domain := inferInstanceAs (LE Nat)

/-- Under the standard model, the definable order is exactly the order on `Nat`,
    crisply: `leF a b` evaluates to certainty iff `⟦a⟧ ≤ ⟦b⟧`. -/
theorem leF_eval_one_iff (env : natModel.Assignment) (a b : ArithQTerm) :
    natModel.evalFormula env (leF a b) = 1 ↔
      natModel.evalTerm env a ≤ natModel.evalTerm env b := by
  -- the existential body, as a crisp predicate of the witness `c`
  have hbody : ∀ c : Nat,
      natModel.evalFormula (Structure.update natModel env c)
        (.equal (addT (Term.rename Nat.succ a) (v 0)) (Term.rename Nat.succ b))
        = (if Nat.add (natModel.evalTerm env a) c = natModel.evalTerm env b
            then (1 : Credence) else 0) := by
    intro c
    have ha : natModel.evalTerm (Structure.update natModel env c)
        (Term.rename Nat.succ a) = natModel.evalTerm env a := by
      rw [Structure.evalTerm_rename]; rfl
    have hb : natModel.evalTerm (Structure.update natModel env c)
        (Term.rename Nat.succ b) = natModel.evalTerm env b := by
      rw [Structure.evalTerm_rename]; rfl
    show natModel.eq (natModel.func .add
        [natModel.evalTerm (Structure.update natModel env c) (Term.rename Nat.succ a),
         c])
        (natModel.evalTerm (Structure.update natModel env c) (Term.rename Nat.succ b))
        = _
    rw [ha, hb]
    rfl
  -- the existential evaluates to the sup of that crisp predicate
  have hcrisp : GradedPredicate.IsCrisp (fun c : Nat =>
      natModel.evalFormula (Structure.update natModel env c)
        (.equal (addT (Term.rename Nat.succ a) (v 0)) (Term.rename Nat.succ b))) := by
    intro c
    simp only [hbody c]
    by_cases h : Nat.add (natModel.evalTerm env a) c = natModel.evalTerm env b
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hch := GradedPredicate.crisp_sup_one_iff _ hcrisp
  show natModel.ex (fun c => natModel.evalFormula (Structure.update natModel env c)
      (.equal (addT (Term.rename Nat.succ a) (v 0)) (Term.rename Nat.succ b))) = 1
    ↔ natModel.evalTerm env a ≤ natModel.evalTerm env b
  constructor
  · intro h
    have hval : iSup (fun c => (natModel.evalFormula (Structure.update natModel env c)
        (.equal (addT (Term.rename Nat.succ a) (v 0))
          (Term.rename Nat.succ b))).val) = 1 := by
      have h' := congrArg Credence.val h
      rw [Credence.one_val] at h'
      exact h'
    obtain ⟨c, hc⟩ := hch.1 hval
    rw [hbody c] at hc
    by_cases hwit : Nat.add (natModel.evalTerm env a) c = natModel.evalTerm env b
    · exact Nat.le.intro hwit
    · rw [if_neg hwit] at hc
      have := congrArg Credence.val hc
      rw [Credence.zero_val, Credence.one_val] at this
      norm_num at this
  · intro hle
    obtain ⟨c, hc⟩ := Nat.le.dest hle
    apply Credence.ext
    rw [Credence.one_val]
    exact hch.2 ⟨c, by rw [hbody c]; exact if_pos hc⟩

/-! ## Quantifier-free and Sigma-1 formula classes -/

/-- Quantifier-free formulas of arithmetic: no `forallE`/`existsE`. -/
def QuantifierFree : ArithQFormula → Prop
  | .top => True
  | .bot => True
  | .atom _ _ => True
  | .equal _ _ => True
  | .neg φ => QuantifierFree φ
  | .conj φ ψ => QuantifierFree φ ∧ QuantifierFree ψ
  | .disj φ ψ => QuantifierFree φ ∧ QuantifierFree ψ
  | .forallE _ => False
  | .existsE _ => False

/-- A quantifier-free arithmetic formula evaluates crisply (0 or 1) in the
    standard model: equality is crisp and the De Morgan connectives preserve
    `{0,1}`. -/
theorem quantifierFree_crisp (env : natModel.Assignment) :
    ∀ φ : ArithQFormula, QuantifierFree φ →
      natModel.evalFormula env φ = 0 ∨ natModel.evalFormula env φ = 1
  | .top, _ => Or.inr rfl
  | .bot, _ => Or.inl rfl
  | .atom p _, _ => p.elim
  | .equal a b, _ => by
      show natModel.eq _ _ = 0 ∨ natModel.eq _ _ = 1
      by_cases h : natModel.evalTerm env a = natModel.evalTerm env b
      · exact Or.inr (by simp [natModel_eq, h])
      · exact Or.inl (by simp [natModel_eq, h])
  | .neg φ, hφ => by
      rcases quantifierFree_crisp env φ hφ with h | h
      · exact Or.inr (by show ~ _ = 1; rw [h]; exact Credence.neg_zero)
      · exact Or.inl (by show ~ _ = 0; rw [h]; exact Credence.neg_one)
  | .conj φ ψ, hφψ => by
      rcases quantifierFree_crisp env φ hφψ.1 with h | h
      · exact Or.inl (by show _ ⊗ _ = 0; rw [h]; exact Credence.zero_conj _)
      · rcases quantifierFree_crisp env ψ hφψ.2 with h' | h'
        · exact Or.inl (by show _ ⊗ _ = 0; rw [h']; exact Credence.conj_zero _)
        · exact Or.inr (by show _ ⊗ _ = 1; rw [h, h']; exact Credence.one_conj _)
  | .disj φ ψ, hφψ => by
      rcases quantifierFree_crisp env φ hφψ.1 with h | h
      · rcases quantifierFree_crisp env ψ hφψ.2 with h' | h'
        · exact Or.inl (by show _ ⊔ _ = 0; rw [h, h']; exact Credence.zero_disj _)
        · exact Or.inr (by show _ ⊔ _ = 1; rw [h']; exact Credence.disj_one _)
      · exact Or.inr (by show _ ⊔ _ = 1; rw [h]; exact Credence.one_disj _)

/-- Sigma-1 formulas: an existential block over a quantifier-free matrix. -/
inductive IsSigmaOne : ArithQFormula → Prop
  | qf {φ : ArithQFormula} (h : QuantifierFree φ) : IsSigmaOne φ
  | ex {φ : ArithQFormula} (h : IsSigmaOne φ) : IsSigmaOne (.existsE φ)

/-! ## Sigma-1 completeness in the standard model

A true existential over a crisp matrix has a numeral witness: this is the
semantic content of Sigma-1 representability, that an existential claim true in
`N` is witnessed by an actual natural number. -/

/-- A single existential over a crisp body is certain iff a witness makes the
    body certain. -/
theorem existsE_crisp_one_iff (env : natModel.Assignment) (φ : ArithQFormula)
    (hcrisp : ∀ c : Nat,
      natModel.evalFormula (Structure.update natModel env c) φ = 0 ∨
      natModel.evalFormula (Structure.update natModel env c) φ = 1) :
    natModel.evalFormula env (.existsE φ) = 1 ↔
      ∃ c : Nat, natModel.evalFormula (Structure.update natModel env c) φ = 1 := by
  show natModel.ex (fun c => natModel.evalFormula (Structure.update natModel env c) φ) = 1
    ↔ _
  have hch := GradedPredicate.crisp_sup_one_iff
    (P := fun c => natModel.evalFormula (Structure.update natModel env c) φ) hcrisp
  constructor
  · intro h
    have hval : iSup (fun c =>
        (natModel.evalFormula (Structure.update natModel env c) φ).val) = 1 := by
      have h' := congrArg Credence.val h
      rw [Credence.one_val] at h'
      exact h'
    exact hch.1 hval
  · rintro ⟨c, hc⟩
    apply Credence.ext; rw [Credence.one_val]; exact hch.2 ⟨c, hc⟩

/-- Sigma-1 completeness for the quantifier-free body: if a quantifier-free
    matrix has a witness, its existential closure is certain in the standard
    model. The converse direction (certain implies witness) is `existsE_crisp`
    above. This is the witness-extraction half of Sigma-1 representability. -/
theorem sigmaOne_witness_complete (env : natModel.Assignment) (φ : ArithQFormula)
    (hqf : QuantifierFree φ) (c : Nat)
    (hc : natModel.evalFormula (Structure.update natModel env c) φ = 1) :
    natModel.evalFormula env (.existsE φ) = 1 :=
  (existsE_crisp_one_iff env φ
    (fun c => quantifierFree_crisp (Structure.update natModel env c) φ hqf)).2 ⟨c, hc⟩

/-! ## The representability target

An object-language formula `P` (with one free variable) *represents* the checker
when, for every code `n`, the standard model designates `P[n̄]` exactly when the
real-free checker accepts `n`. The recursion-theoretic side, `checkCodeNat`, is
already a total computable decision (`Structure.checkCodeNat`,
`provability_representable`); a representing `P` is the classical arithmetization
of that decision into the object arithmetic. -/

/-- The numeral for `n`: `S (S ... (S 0))`. -/
def numeral : Nat → ArithQTerm
  | 0 => zeroT
  | n + 1 => succT (numeral n)

@[simp] theorem eval_numeral (env : natModel.Assignment) :
    ∀ n : Nat, natModel.evalTerm env (numeral n) = n
  | 0 => rfl
  | n + 1 => by
      show natModel.func .succ [natModel.evalTerm env (numeral n)] = n + 1
      rw [eval_numeral env n]
      rfl

/-- `P` represents the real-free checker `checkCodeNat` when designation of the
    instantiated formula tracks acceptance, code by code. Constructing such a `P`
    is the object-language arithmetization that closes PA-internal
    representability; the predicate it must satisfy is named here exactly. -/
def RepresentsChecker (P : ArithQFormula) : Prop :=
  ∀ n : Nat, ∀ env : natModel.Assignment,
    natModel.evalFormula env (Formula.instantiate (numeral n) P) = 1 ↔
      Structure.checkCodeNat n = true

/-! ## The second-incompleteness boundary

Even granting a representing `P`, the second incompleteness theorem does not
internalize in Cred as an object-language conditional. Its proof needs Loeb's
derivability conditions, hence an internal implication with modus ponens,
conditional proof, and contraction. The Curry block proves no total operation on
credences has all three, so the internal Loeb arrow does not exist. The boundary
is structural, not a missing lemma. -/

/-- No total internal conditional carries the Loeb / Hilbert-Bernays conditions:
    modus ponens, conditional proof, and contraction cannot coexist on credences.
    Hence the second incompleteness theorem has no internal-arrow derivation in
    Cred, regardless of any representing provability formula. -/
theorem no_internal_loeb_arrow :
    ¬ ∃ f : Credence → Credence → Credence,
        Credence.MP f ∧ Credence.CP f ∧ Credence.Contraction f :=
  Credence.curry_block

end arithQ
end Foundation
end Cred
