/-
  Cred Foundation: the modulo graph and Goedel's beta extraction

  Goedel's beta function reads the entries of a finite sequence out of two
  numbers by remainder arithmetic: `beta a d i = a % (1 + (i+1)*d)`. This gives
  bounded sequence access without recursion, the step that turns the pairing and
  list coding of the previous bricks into arithmetized course-of-values. The
  modulo relation itself is the graph `∃q, a = q*m + r ∧ r < m`, a single
  existential over a crisp matrix, so Sigma-1 witness extraction applies
  directly. `betaGraph` is the modulo graph at the modulus term `S((S i)*d)`,
  which is positive outright; its representability needs no side condition.
-/

import Cred.Foundation.SeqCoding

namespace Cred
namespace Foundation
namespace arithQ

open Credence

-- the remainder statement needs `%` and the literal `0` on the domain
instance : Mod natModel.Domain := inferInstanceAs (Mod Nat)
instance : OfNat natModel.Domain 0 := inferInstanceAs (OfNat Nat 0)

/-! ## The modulo graph -/

/-- The graph of the modulo relation: `r = a % m` as `∃q, a = q*m + r ∧ r < m`.
    The quotient `q` is the bound witness `v 0`; the parameters shift under the
    binder by `Nat.succ`. -/
def modGraph (a m r : ArithQTerm) : ArithQFormula :=
  .existsE (.conj
    (.equal (Term.rename Nat.succ a)
      (addT (mulT (v 0) (Term.rename Nat.succ m)) (Term.rename Nat.succ r)))
    (ltF (Term.rename Nat.succ r) (Term.rename Nat.succ m)))

/-- A parameter shifted under the binder evaluates as it did outside. -/
private theorem eval_rename_succ (env : natModel.Assignment)
    (q : natModel.Domain) (t : ArithQTerm) :
    natModel.evalTerm (Structure.update natModel env q)
        (Term.rename Nat.succ t) =
      natModel.evalTerm env t := by
  rw [Structure.evalTerm_rename]
  rfl

/-- Witness arithmetic: a quotient `q` with `a = q*m + r` and `r < m` exists
    exactly when `r` is the remainder of `a` by `m`. -/
private theorem mod_witness_iff (a m r : Nat) (hm : 0 < m) :
    (∃ q : Nat, a = q * m + r ∧ r < m) ↔ r = a % m := by
  constructor
  · rintro ⟨q, hq, hr⟩
    rw [hq, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  · intro h
    refine ⟨a / m, ?_, ?_⟩
    · rw [h, Nat.mul_comm]
      exact (Nat.div_add_mod a m).symm
    · rw [h]
      exact Nat.mod_lt a hm

/-- Term-level evaluation of the modulo graph: designated exactly when `⟦r⟧` is
    the remainder of `⟦a⟧` by `⟦m⟧`, for any positive modulus term. -/
private theorem modGraph_eval_one_iff (env : natModel.Assignment)
    (A M R : ArithQTerm) (hm : 0 < natModel.evalTerm env M) :
    natModel.evalFormula env (modGraph A M R) = 1 ↔
      natModel.evalTerm env R =
        natModel.evalTerm env A % natModel.evalTerm env M := by
  -- the existential body, designated at witness `q` iff `a = q*m + r ∧ r < m`
  have hbody : ∀ q : natModel.Domain,
      natModel.evalFormula (Structure.update natModel env q)
        (.conj
          (.equal (Term.rename Nat.succ A)
            (addT (mulT (v 0) (Term.rename Nat.succ M))
              (Term.rename Nat.succ R)))
          (ltF (Term.rename Nat.succ R) (Term.rename Nat.succ M))) = 1 ↔
        natModel.evalTerm env A =
            q * natModel.evalTerm env M + natModel.evalTerm env R ∧
          natModel.evalTerm env R < natModel.evalTerm env M := by
    intro q
    have hrhs : natModel.evalTerm (Structure.update natModel env q)
        (addT (mulT (v 0) (Term.rename Nat.succ M)) (Term.rename Nat.succ R)) =
          q * natModel.evalTerm env M + natModel.evalTerm env R := by
      show natModel.func .add
          [natModel.func .mul
            [Structure.update natModel env q 0,
             natModel.evalTerm (Structure.update natModel env q)
               (Term.rename Nat.succ M)],
           natModel.evalTerm (Structure.update natModel env q)
             (Term.rename Nat.succ R)] = _
      rw [eval_rename_succ, eval_rename_succ]
      rfl
    show natModel.evalFormula (Structure.update natModel env q)
        (.equal (Term.rename Nat.succ A)
          (addT (mulT (v 0) (Term.rename Nat.succ M))
            (Term.rename Nat.succ R))) ⊗
      natModel.evalFormula (Structure.update natModel env q)
        (ltF (Term.rename Nat.succ R) (Term.rename Nat.succ M)) = 1 ↔ _
    rw [conj_crisp_one_iff (eqAtom_crisp _ _ _) (ltF_crisp _ _ _),
      eqAtom_eval_one_iff, ltF_eval_one_iff, eval_rename_succ, hrhs,
      eval_rename_succ, eval_rename_succ]
  -- the body is crisp at every witness, so the existential is the witness claim
  have hcrisp : ∀ q : Nat,
      natModel.evalFormula (Structure.update natModel env q)
        (.conj
          (.equal (Term.rename Nat.succ A)
            (addT (mulT (v 0) (Term.rename Nat.succ M))
              (Term.rename Nat.succ R)))
          (ltF (Term.rename Nat.succ R) (Term.rename Nat.succ M))) = 0 ∨
      natModel.evalFormula (Structure.update natModel env q)
        (.conj
          (.equal (Term.rename Nat.succ A)
            (addT (mulT (v 0) (Term.rename Nat.succ M))
              (Term.rename Nat.succ R)))
          (ltF (Term.rename Nat.succ R) (Term.rename Nat.succ M))) = 1 :=
    fun _ => conj_crisp (eqAtom_crisp _ _ _) (ltF_crisp _ _ _)
  rw [modGraph, existsE_crisp_one_iff env _ hcrisp]
  exact (exists_congr hbody).trans (mod_witness_iff _ _ _ hm)

/-- Numeral-level representability: the modulo graph at numerals is designated
    exactly when `r = a % m`, for positive `m`. -/
theorem modGraph_represents (a m r : Nat) (env : natModel.Assignment)
    (hm : 0 < m) :
    natModel.evalFormula env
        (modGraph (numeral a) (numeral m) (numeral r)) = 1 ↔
      r = a % m := by
  rw [modGraph_eval_one_iff env _ _ _ (by rw [eval_numeral]; exact hm),
    eval_numeral, eval_numeral, eval_numeral]

/-! ## Goedel's beta extraction -/

/-- Goedel's beta graph: `v = a % (1 + (i+1)*d)`, the modulo graph at the
    modulus term `S ((S i) * d)`. -/
def betaGraph (a d i v : ArithQTerm) : ArithQFormula :=
  modGraph a (succT (mulT (succT i) d)) v

/-- Numeral-level representability of beta extraction. The modulus is a
    successor term, hence positive; no side condition remains. -/
theorem betaGraph_represents (a d i v : Nat) (env : natModel.Assignment) :
    natModel.evalFormula env
        (betaGraph (numeral a) (numeral d) (numeral i) (numeral v)) = 1 ↔
      v = a % (1 + (i + 1) * d) := by
  have hmod : natModel.evalTerm env
      (succT (mulT (succT (numeral i)) (numeral d))) =
        ((1 + (i + 1) * d : Nat)) := by
    show natModel.func .succ
        [natModel.func .mul
          [natModel.func .succ [natModel.evalTerm env (numeral i)],
           natModel.evalTerm env (numeral d)]] = _
    rw [eval_numeral, eval_numeral]
    show (i + 1) * d + 1 = 1 + (i + 1) * d
    exact Nat.add_comm _ _
  rw [betaGraph,
    modGraph_eval_one_iff env _ _ _
      (by rw [hmod]
          exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 _)),
    eval_numeral, eval_numeral, hmod]

end arithQ
end Foundation
end Cred
