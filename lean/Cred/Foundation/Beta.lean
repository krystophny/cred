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
import Mathlib.Logic.Godel.GodelBetaFunction

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

/-! ## Single-code beta access

`Nat.beta n i = n.unpair.1 % ((i+1) * n.unpair.2 + 1)` packs the two beta
arguments into one code `n`. The object formula binds the two unpaired halves
existentially: `a` for `n.unpair.1`, `d` for `n.unpair.2`, then reads the
remainder through `betaGraph`. Both binders sit over a crisp matrix, so the
Sigma-1 witness extraction applies twice. -/

/-- Lift a term past two fresh binders. -/
private def shift2 (t : ArithQTerm) : ArithQTerm :=
  Term.rename (Nat.succ ∘ Nat.succ) t

/-- A term shifted under two binders evaluates as it did outside. -/
private theorem eval_shift2 (env : natModel.Assignment)
    (a d : natModel.Domain) (t : ArithQTerm) :
    natModel.evalTerm
        (Structure.update natModel (Structure.update natModel env a) d)
        (shift2 t) =
      natModel.evalTerm env t := by
  rw [shift2, Structure.evalTerm_rename]
  rfl

/-- A disjunction of crisp credences is crisp. -/
private theorem disj_crisp {a b : Credence}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a ⊔ b = 0 ∨ a ⊔ b = 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst ha <;> subst hb <;>
    simp [Credence.zero_disj, Credence.disj_zero, Credence.disj_one,
      Credence.one_disj]

/-- An existential over a crisp body evaluates crisply: the supremum of a
    `{0,1}`-valued family is `1` when a witness exists and `0` otherwise. -/
private theorem existsE_crisp (env : natModel.Assignment) (φ : ArithQFormula)
    (hcrisp : ∀ c : Nat,
      natModel.evalFormula (Structure.update natModel env c) φ = 0 ∨
      natModel.evalFormula (Structure.update natModel env c) φ = 1) :
    natModel.evalFormula env (.existsE φ) = 0 ∨
      natModel.evalFormula env (.existsE φ) = 1 := by
  by_cases h : ∃ c : Nat,
      natModel.evalFormula (Structure.update natModel env c) φ = 1
  · exact Or.inr ((existsE_crisp_one_iff env φ hcrisp).2 h)
  · left
    have hzero : (fun c : Nat =>
        natModel.evalFormula (Structure.update natModel env c) φ) =
          fun _ : Nat => (0 : Credence) := by
      funext c
      rcases hcrisp c with h0 | h1
      · exact h0
      · exact absurd ⟨c, h1⟩ h
    show natModel.ex (fun c : Nat =>
        natModel.evalFormula (Structure.update natModel env c) φ) = 0
    exact (congrArg natModel.ex hzero).trans natModel_quantifierLaws.ex_zero

/-- A crisp conjunction at the formula level is designated iff both conjuncts
    are. -/
private theorem conjFormula_crisp_one_iff (env : natModel.Assignment)
    (φ ψ : ArithQFormula)
    (hφ : natModel.evalFormula env φ = 0 ∨ natModel.evalFormula env φ = 1)
    (hψ : natModel.evalFormula env ψ = 0 ∨ natModel.evalFormula env ψ = 1) :
    natModel.evalFormula env (.conj φ ψ) = 1 ↔
      natModel.evalFormula env φ = 1 ∧ natModel.evalFormula env ψ = 1 := by
  show natModel.evalFormula env φ ⊗ natModel.evalFormula env ψ = 1 ↔ _
  exact conj_crisp_one_iff hφ hψ

/-- The pairing graph evaluates crisply at every term tuple. -/
private theorem pairGraph_crisp (env : natModel.Assignment)
    (x y z : ArithQTerm) :
    natModel.evalFormula env (pairGraph x y z) = 0 ∨
      natModel.evalFormula env (pairGraph x y z) = 1 := by
  rw [pairGraph]
  exact disj_crisp
    (conj_crisp (ltF_crisp env x y) (eqAtom_crisp env z (addT (mulT y y) x)))
    (conj_crisp (leF_crisp env y x)
      (eqAtom_crisp env z (addT (addT (mulT x x) x) y)))

/-- The unpairing graph evaluates crisply at every term tuple. -/
private theorem unpairGraph_crisp (env : natModel.Assignment)
    (z x y : ArithQTerm) :
    natModel.evalFormula env (unpairGraph z x y) = 0 ∨
      natModel.evalFormula env (unpairGraph z x y) = 1 :=
  pairGraph_crisp env x y z

/-- The modulo graph evaluates crisply at every term tuple. -/
private theorem modGraph_crisp (env : natModel.Assignment)
    (a m r : ArithQTerm) :
    natModel.evalFormula env (modGraph a m r) = 0 ∨
      natModel.evalFormula env (modGraph a m r) = 1 := by
  rw [modGraph]
  exact existsE_crisp env _
    (fun _ => conj_crisp (eqAtom_crisp _ _ _) (ltF_crisp _ _ _))

/-- The beta graph evaluates crisply at every term tuple. -/
private theorem betaGraph_crisp (env : natModel.Assignment)
    (a d i w : ArithQTerm) :
    natModel.evalFormula env (betaGraph a d i w) = 0 ∨
      natModel.evalFormula env (betaGraph a d i w) = 1 :=
  modGraph_crisp env a (succT (mulT (succT i) d)) w

/-- The unpairing graph at arbitrary terms: designated exactly when `⟦z⟧`
    unpairs into `(⟦x⟧, ⟦y⟧)`. -/
private theorem unpairGraph_eval_one_iff (env : natModel.Assignment)
    (z x y : ArithQTerm) :
    natModel.evalFormula env (unpairGraph z x y) = 1 ↔
      Nat.unpair (natModel.evalTerm env z) =
        (natModel.evalTerm env x, natModel.evalTerm env y) := by
  rw [unpairGraph, pairGraph_eval_one_iff, pair_eq_iff_unpair]

/-- The beta graph at arbitrary terms: designated exactly when `⟦w⟧` is the
    remainder of `⟦a⟧` by `1 + (⟦i⟧+1) * ⟦d⟧`. -/
private theorem betaGraph_eval_one_iff (env : natModel.Assignment)
    (A D I W : ArithQTerm) :
    natModel.evalFormula env (betaGraph A D I W) = 1 ↔
      natModel.evalTerm env W =
        natModel.evalTerm env A %
          (1 + (natModel.evalTerm env I + 1) * natModel.evalTerm env D) := by
  have hmod : natModel.evalTerm env (succT (mulT (succT I) D)) =
      1 + (natModel.evalTerm env I + 1) * natModel.evalTerm env D := by
    show natModel.func .succ
        [natModel.func .mul
          [natModel.func .succ [natModel.evalTerm env I],
           natModel.evalTerm env D]] = _
    show (natModel.evalTerm env I + 1) * natModel.evalTerm env D + 1 = _
    exact Nat.add_comm _ _
  rw [betaGraph,
    modGraph_eval_one_iff env _ _ _
      (by rw [hmod]
          exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 _)),
    hmod]

/-- The crisp matrix of the single-code beta graph: unpair the code into the
    two bound halves `a := v 1`, `d := v 0`, then read the remainder. -/
private def betaNBody (n i w : ArithQTerm) : ArithQFormula :=
  .conj (unpairGraph (shift2 n) (Term.var 1) (Term.var 0))
    (betaGraph (Term.var 1) (Term.var 0) (shift2 i) (shift2 w))

/-- The single-code Goedel beta graph: `v = Nat.beta n i`, with the two
    unpaired halves of the code bound existentially over the crisp matrix. -/
def betaNGraph (n i v : ArithQTerm) : ArithQFormula :=
  .existsE (.existsE (betaNBody n i v))

/-- The matrix at numerals and witnesses `(a, d)`: designated exactly when
    `(a, d)` unpairs `n` and `k` is the corresponding remainder. -/
private theorem betaNBody_eval_one_iff (env : natModel.Assignment)
    (n i k a d : Nat) :
    natModel.evalFormula
        (Structure.update natModel (Structure.update natModel env a) d)
        (betaNBody (numeral n) (numeral i) (numeral k)) = 1 ↔
      (Nat.unpair n = (a, d) ∧ k = a % (1 + (i + 1) * d)) := by
  have en : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (shift2 (numeral n)) = n := by
    rw [eval_shift2, eval_numeral]
  have ei : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (shift2 (numeral i)) = i := by
    rw [eval_shift2, eval_numeral]
  have ek : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (shift2 (numeral k)) = k := by
    rw [eval_shift2, eval_numeral]
  have ea : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (Term.var 1) = a := rfl
  have ed : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (Term.var 0) = d := rfl
  rw [betaNBody,
    conjFormula_crisp_one_iff _ _ _ (unpairGraph_crisp _ _ _ _)
      (betaGraph_crisp _ _ _ _ _),
    unpairGraph_eval_one_iff, betaGraph_eval_one_iff,
    en, ei, ek, ea, ed]

/-- Witness arithmetic: the two unpaired halves of `n` exist exactly when `k`
    is `Nat.beta n i`; the modulus commutes between `1 + (i+1)*d` and
    `(i+1)*d + 1`. -/
private theorem betaN_witness_iff (n i k : Nat) :
    (∃ a : Nat, ∃ d : Nat,
        Nat.unpair n = (a, d) ∧ k = a % (1 + (i + 1) * d)) ↔
      k = Nat.beta n i := by
  constructor
  · rintro ⟨a, d, hpair, hk⟩
    have ha : (Nat.unpair n).1 = a := by rw [hpair]
    have hd : (Nat.unpair n).2 = d := by rw [hpair]
    show k = (Nat.unpair n).1 % ((i + 1) * (Nat.unpair n).2 + 1)
    rw [ha, hd, Nat.add_comm ((i + 1) * d) 1]
    exact hk
  · intro hk
    refine ⟨(Nat.unpair n).1, (Nat.unpair n).2, rfl, ?_⟩
    rw [Nat.add_comm 1 ((i + 1) * (Nat.unpair n).2)]
    exact hk

/-- Numeral-level representability of single-code beta access: the graph at
    numerals is designated exactly when `v = Nat.beta n i`. -/
theorem betaNGraph_represents (n i v : Nat) (env : natModel.Assignment) :
    natModel.evalFormula env
        (betaNGraph (numeral n) (numeral i) (numeral v)) = 1 ↔
      v = Nat.beta n i := by
  have hbody : ∀ a d : Nat,
      natModel.evalFormula
          (Structure.update natModel (Structure.update natModel env a) d)
          (betaNBody (numeral n) (numeral i) (numeral v)) = 0 ∨
        natModel.evalFormula
          (Structure.update natModel (Structure.update natModel env a) d)
          (betaNBody (numeral n) (numeral i) (numeral v)) = 1 := by
    intro a d
    rw [betaNBody]
    exact conj_crisp (unpairGraph_crisp _ _ _ _) (betaGraph_crisp _ _ _ _ _)
  have hinner : ∀ a : Nat,
      natModel.evalFormula (Structure.update natModel env a)
          (.existsE (betaNBody (numeral n) (numeral i) (numeral v))) = 0 ∨
        natModel.evalFormula (Structure.update natModel env a)
          (.existsE (betaNBody (numeral n) (numeral i) (numeral v))) = 1 :=
    fun a => existsE_crisp _ _ (hbody a)
  rw [betaNGraph, existsE_crisp_one_iff env _ hinner]
  refine Iff.trans (exists_congr fun a => ?_) (betaN_witness_iff n i v)
  rw [existsE_crisp_one_iff _ _ (hbody a)]
  exact exists_congr fun d => betaNBody_eval_one_iff env n i v a d

end arithQ
end Foundation
end Cred
