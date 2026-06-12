/-
  Cred Foundation: list coding over the Robinson Q signature

  The Goedel numbering codes lists by `nil = 0` and `cons h t = Nat.pair h t + 1`,
  so a code is nil exactly when it is zero, and a nonempty code is the successor
  of a pair. `isNilGraph` is the zero test. `consGraph` reuses the two guarded
  branches of `pairGraph` with a successor wrapped around each right-hand side,
  which encodes `l = Nat.pair h t + 1` without a predecessor term or a bound
  witness. Both graphs come with numeral-level representability proofs in the
  standard model; head/tail readback follows from the pairing bijection.
-/

import Cred.Foundation.Pairing

namespace Cred
namespace Foundation
namespace arithQ

open Credence

-- the cons branches end in `+ 1`; expose the literal on the domain
instance : OfNat natModel.Domain 1 := inferInstanceAs (OfNat Nat 1)

/-! ## The nil graph -/

/-- The nil code is `0`: `isNilGraph l := (l = 0)`. -/
def isNilGraph (l : ArithQTerm) : ArithQFormula := .equal l zeroT

/-- Numeral-level representability of the nil test. -/
theorem isNilGraph_represents (l : Nat) (env : natModel.Assignment) :
    natModel.evalFormula env (isNilGraph (numeral l)) = 1 ↔ l = 0 := by
  rw [isNilGraph, eqAtom_eval_one_iff, eval_numeral]
  exact ⟨fun h => h, fun h => h⟩

/-! ## The cons graph -/

/-- The graph of the cons code `l = Nat.pair h t + 1`: the pairing graph's two
    guarded branches with a successor on each right-hand side. -/
def consGraph (h t l : ArithQTerm) : ArithQFormula :=
  .disj
    (.conj (ltF h t) (.equal l (succT (addT (mulT t t) h))))
    (.conj (leF t h) (.equal l (succT (addT (addT (mulT h h) h) t))))

/-- The two guarded branches, against `Nat.pair`'s definition shifted by one. -/
private theorem cons_branch_iff (xv yv zv : Nat) :
    ((xv < yv ∧ zv = yv * yv + xv + 1) ∨
        (yv ≤ xv ∧ zv = xv * xv + xv + yv + 1)) ↔
      zv = Nat.pair xv yv + 1 := by
  unfold Nat.pair
  by_cases hlt : xv < yv
  · rw [if_pos hlt]
    constructor
    · rintro (⟨_, hz⟩ | ⟨hle, _⟩)
      · exact hz
      · exact absurd hlt (Nat.not_lt.mpr hle)
    · exact fun hz => Or.inl ⟨hlt, hz⟩
  · rw [if_neg hlt]
    constructor
    · rintro (⟨hlt', _⟩ | ⟨_, hz⟩)
      · exact absurd hlt' hlt
      · exact hz
    · exact fun hz => Or.inr ⟨Nat.le_of_not_lt hlt, hz⟩

/-- The cons graph is designated in the standard model exactly when `l` is
    `Nat.pair h t + 1`. -/
theorem consGraph_eval_one_iff (env : natModel.Assignment) (x y z : ArithQTerm) :
    natModel.evalFormula env (consGraph x y z) = 1 ↔
      (natModel.evalTerm env z : Nat) =
        Nat.pair (natModel.evalTerm env x) (natModel.evalTerm env y) + (1 : Nat) := by
  -- crispness of the two branch conjunctions
  have h1 : natModel.evalFormula env
        (.conj (ltF x y) (.equal z (succT (addT (mulT y y) x)))) = 0 ∨
      natModel.evalFormula env
        (.conj (ltF x y) (.equal z (succT (addT (mulT y y) x)))) = 1 :=
    conj_crisp (ltF_crisp env x y)
      (eqAtom_crisp env z (succT (addT (mulT y y) x)))
  have h2 : natModel.evalFormula env
        (.conj (leF y x) (.equal z (succT (addT (addT (mulT x x) x) y)))) = 0 ∨
      natModel.evalFormula env
        (.conj (leF y x) (.equal z (succT (addT (addT (mulT x x) x) y)))) = 1 :=
    conj_crisp (leF_crisp env y x)
      (eqAtom_crisp env z (succT (addT (addT (mulT x x) x) y)))
  -- the two branches, read off crisply
  have hc1 : natModel.evalFormula env
        (.conj (ltF x y) (.equal z (succT (addT (mulT y y) x)))) = 1 ↔
      natModel.evalTerm env x < natModel.evalTerm env y ∧
        natModel.evalTerm env z =
          natModel.evalTerm env y * natModel.evalTerm env y +
            natModel.evalTerm env x + 1 := by
    show natModel.evalFormula env (ltF x y) ⊗
        natModel.evalFormula env (.equal z (succT (addT (mulT y y) x))) = 1 ↔ _
    rw [conj_crisp_one_iff (ltF_crisp env x y)
          (eqAtom_crisp env z (succT (addT (mulT y y) x))),
      ltF_eval_one_iff, eqAtom_eval_one_iff]
    exact Iff.rfl
  have hc2 : natModel.evalFormula env
        (.conj (leF y x) (.equal z (succT (addT (addT (mulT x x) x) y)))) = 1 ↔
      natModel.evalTerm env y ≤ natModel.evalTerm env x ∧
        natModel.evalTerm env z =
          natModel.evalTerm env x * natModel.evalTerm env x +
            natModel.evalTerm env x + natModel.evalTerm env y + 1 := by
    show natModel.evalFormula env (leF y x) ⊗
        natModel.evalFormula env
          (.equal z (succT (addT (addT (mulT x x) x) y))) = 1 ↔ _
    rw [conj_crisp_one_iff (leF_crisp env y x)
          (eqAtom_crisp env z (succT (addT (addT (mulT x x) x) y))),
      leF_eval_one_iff, eqAtom_eval_one_iff]
    exact Iff.rfl
  -- assemble: disj of two crisp conjunctions matches the shifted case split
  show natModel.evalFormula env
      (.conj (ltF x y) (.equal z (succT (addT (mulT y y) x))))
      ⊔ natModel.evalFormula env (.conj (leF y x)
          (.equal z (succT (addT (addT (mulT x x) x) y)))) = 1 ↔ _
  rw [disj_crisp_one_iff h1 h2, hc1, hc2]
  exact cons_branch_iff _ _ _

/-- Numeral-level representability: the cons graph at numerals is designated
    exactly when `l = Nat.pair h t + 1`. -/
theorem consGraph_represents (h t l : Nat) (env : natModel.Assignment) :
    natModel.evalFormula env
        (consGraph (numeral h) (numeral t) (numeral l)) = 1 ↔
      l = Nat.pair h t + 1 := by
  rw [consGraph_eval_one_iff, eval_numeral, eval_numeral, eval_numeral]

/-! ## Head/tail readback for nonempty codes

A nonempty code `l` is the successor of the pair of its head and tail, so the
pairing bijection reads both back off `l - 1`. -/

/-- For a positive code, the cons graph at numerals is designated exactly when
    `(h, t)` is the unpairing of `l - 1`. -/
theorem consGraph_head_tail (h t l : Nat) (env : natModel.Assignment)
    (hl : 0 < l) :
    natModel.evalFormula env
        (consGraph (numeral h) (numeral t) (numeral l)) = 1 ↔
      (h, t) = Nat.unpair (l - 1) := by
  rw [consGraph_represents]
  constructor
  · intro hc
    rw [hc, Nat.add_sub_cancel, Nat.unpair_pair]
  · intro hu
    have hp : l - 1 = Nat.pair h t :=
      (pair_eq_iff_unpair h t (l - 1)).2 hu.symm
    rw [← hp]
    omega

end arithQ
end Foundation
end Cred
