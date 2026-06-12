/-
  Cred Foundation CodingNat

  A non-degenerate witness for the DiagonalCoding interface.  The domain is
  Nat, codes are numerals of an injective Goedel numbering, and selfApp is the
  real diagonal map computed through a decoder.  Unlike the one-point witness,
  distinct formulas receive distinct codes and selfApp_diag holds by genuine
  computation of substitution on codes rather than by collapse.
-/

import Cred.Foundation.Diagonal
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

namespace Cred
namespace Foundation

open Credence

/-! ## Object language fixed to the coding alphabet

We work with `Func = Option Nat` (a self-application symbol `none` plus a
numeral literal `some k`) and the single provability predicate `Pred = Unit`. -/

abbrev NatFunc := Option Nat
abbrev NatPred := Unit
abbrev NatTerm := Term NatFunc
abbrev NatFormula := Formula NatFunc NatPred

namespace natCoding

/-- Encode the function alphabet: `none ↦ 0`, `some k ↦ k + 1`. -/
def gnumFunc : NatFunc → Nat
  | none => 0
  | some k => k + 1

theorem gnumFunc_injective : Function.Injective gnumFunc := by
  intro a b h
  cases a <;> cases b <;> simp_all [gnumFunc]

mutual

/-- Injective Goedel numbering of terms. -/
def gnumTerm : NatTerm → Nat
  | .var n => Nat.pair 0 n
  | .app f args => Nat.pair 1 (Nat.pair (gnumFunc f) (gnumTermList args))

/-- Injective Goedel numbering of argument lists (`0` is the empty list). -/
def gnumTermList : List NatTerm → Nat
  | [] => 0
  | t :: ts => Nat.pair (gnumTerm t) (gnumTermList ts) + 1

end

mutual

theorem gnumTerm_injective :
    ∀ {s t : NatTerm}, gnumTerm s = gnumTerm t → s = t
  | .var m, .var n, h => by
      simp only [gnumTerm, Nat.pair_eq_pair] at h; exact h.2 ▸ rfl
  | .var _, .app _ _, h => by simp [gnumTerm, Nat.pair_eq_pair] at h
  | .app _ _, .var _, h => by simp [gnumTerm, Nat.pair_eq_pair] at h
  | .app f args, .app g args', h => by
      simp only [gnumTerm, Nat.pair_eq_pair] at h
      obtain ⟨hf, hargs⟩ := h.2
      rw [gnumFunc_injective hf, gnumTermList_injective hargs]

theorem gnumTermList_injective :
    ∀ {ss ts : List NatTerm}, gnumTermList ss = gnumTermList ts → ss = ts
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [gnumTermList] at h
  | _ :: _, [], h => by simp [gnumTermList] at h
  | s :: ss, t :: ts, h => by
      simp only [gnumTermList, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
      rw [gnumTerm_injective h.1, gnumTermList_injective h.2]

end

/-- Injective Goedel numbering of formulas.  Each constructor occupies a
    distinct tag, so the first pairing component separates them. -/
def gnumFormula : NatFormula → Nat
  | .top => Nat.pair 0 0
  | .bot => Nat.pair 1 0
  | .atom _ args => Nat.pair 2 (gnumTermList args)
  | .equal a b => Nat.pair 3 (Nat.pair (gnumTerm a) (gnumTerm b))
  | .neg φ => Nat.pair 4 (gnumFormula φ)
  | .conj φ ψ => Nat.pair 5 (Nat.pair (gnumFormula φ) (gnumFormula ψ))
  | .disj φ ψ => Nat.pair 6 (Nat.pair (gnumFormula φ) (gnumFormula ψ))
  | .forallE φ => Nat.pair 7 (gnumFormula φ)
  | .existsE φ => Nat.pair 8 (gnumFormula φ)

theorem gnumFormula_injective : Function.Injective gnumFormula := by
  intro φ
  induction φ with
  | top =>
      intro ψ h
      cases ψ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | rfl
        | (exfalso; omega)
  | bot =>
      intro ψ h
      cases ψ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | rfl
        | (exfalso; omega)
  | atom p args =>
      intro ψ h
      cases ψ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | (exfalso; omega)
        | (cases p; rw [gnumTermList_injective h.2])
  | equal a b =>
      intro ψ h
      cases ψ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | (exfalso; omega)
        | (obtain ⟨ha, hb⟩ := h.2; rw [gnumTerm_injective ha, gnumTerm_injective hb])
  | neg φ ih =>
      intro ψ h
      cases ψ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | (exfalso; omega)
        | rw [ih h.2]
  | conj φ ψ ihφ ihψ =>
      intro χ h
      cases χ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | (exfalso; omega)
        | (obtain ⟨hl, hr⟩ := h.2; rw [ihφ hl, ihψ hr])
  | disj φ ψ ihφ ihψ =>
      intro χ h
      cases χ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | (exfalso; omega)
        | (obtain ⟨hl, hr⟩ := h.2; rw [ihφ hl, ihψ hr])
  | forallE φ ih =>
      intro ψ h
      cases ψ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | (exfalso; omega)
        | rw [ih h.2]
  | existsE φ ih =>
      intro ψ h
      cases ψ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | (exfalso; omega)
        | rw [ih h.2]

instance : Nonempty NatFormula := ⟨Formula.top⟩

/-- Total left inverse of the numbering, recovered from injectivity. -/
noncomputable def decodeFormula : Nat → NatFormula :=
  Function.invFun gnumFormula

theorem decodeFormula_gnum (φ : NatFormula) :
    decodeFormula (gnumFormula φ) = φ :=
  Function.leftInverse_invFun gnumFormula_injective φ

/-! ## The concrete structure

Domain `= Nat`.  Numerals `some k` evaluate to `k`; the self-application
symbol `none` decodes its single argument, instantiates the decoded formula
with the numeral of that argument, and re-encodes.  Other shapes are inert. -/

/-- Numeral term for a Goedel code. -/
def numeral (k : Nat) : NatTerm := Term.app (some k) []

/-- The diagonal function on codes: decode, self-instantiate, re-encode. -/
noncomputable def diagFunc : Nat → Nat
  | n => gnumFormula ((decodeFormula n).instantiate (numeral n))

noncomputable def natStructure : Structure NatFunc NatPred where
  Domain := Nat
  witness := 0
  func
    | none, [n] => diagFunc n
    | some k, _ => k
    | none, _ => 0
  pred _ _ := half
  eq a b := if a = b then 1 else 0
  all f := f 0
  ex f := f 0

theorem natStructure_func_numeral (k : Nat) (xs : List Nat) :
    natStructure.func (some k) xs = k := rfl

@[simp] theorem evalTerm_numeral (env : natStructure.Assignment) (k : Nat) :
    natStructure.evalTerm env (numeral k) = k := rfl

/-- The non-degenerate coding: codes are numerals of the injective numbering,
    selfApp is the real diagonal function. -/
noncomputable def diagCoding : natStructure.DiagonalCoding where
  code φ := numeral (gnumFormula φ)
  selfApp := none
  code_closed _ _ _ := rfl
  selfApp_diag φ env := by
    -- evalTerm (app none [numeral (gnum φ)]) computes diagFunc (gnum φ);
    -- the decoder recovers φ, so this equals gnum (φ.instantiate (code φ)).
    show natStructure.func none [gnumFormula φ] =
      gnumFormula (φ.instantiate (numeral (gnumFormula φ)))
    show diagFunc (gnumFormula φ) =
      gnumFormula (φ.instantiate (numeral (gnumFormula φ)))
    rw [diagFunc, decodeFormula_gnum]

/-! ## Genuine non-degeneracy: distinct formulas get distinct evaluated codes. -/

theorem code_eval (φ : NatFormula) (env : natStructure.Assignment) :
    natStructure.evalTerm env (diagCoding.code φ) = gnumFormula φ := rfl

/-- Faithfulness: the evaluated code is injective on formulas.  This is the
    central non-degeneracy property the one-point witness lacks. -/
theorem code_eval_injective (env : natStructure.Assignment) :
    Function.Injective
      (fun φ : NatFormula => natStructure.evalTerm env (diagCoding.code φ)) := by
  intro φ ψ h
  exact gnumFormula_injective (by simpa [code_eval] using h)

/-- Distinct formulas never share an evaluated code. -/
theorem code_eval_distinct (φ ψ : NatFormula) (env : natStructure.Assignment)
    (h : φ ≠ ψ) :
    natStructure.evalTerm env (diagCoding.code φ) ≠
      natStructure.evalTerm env (diagCoding.code ψ) :=
  fun heq => h (code_eval_injective env heq)

/-! ## Reflection witness and the graded Goedel half theorem

The provability predicate is interpreted as the constant `half`.  This is the
only fixed point of negation, so reflection at the Goedel code holds and the
sentence is pinned to `half` through the genuinely computed diagonal. -/

theorem nat_godel_reflects (env : natStructure.Assignment) :
    natStructure.pred ()
        [natStructure.evalTerm env
          (diagCoding.code (diagCoding.godel ()))] =
      natStructure.evalFormula env (diagCoding.godel ()) := by
  rw [diagCoding.godel_eval () env]
  exact liar_fixed_point.symm

theorem nat_godel_half (env : natStructure.Assignment) :
    natStructure.evalFormula env (diagCoding.godel ()) = half :=
  diagCoding.godel_eval_half () env (nat_godel_reflects env)

theorem nat_godel_half_of_reflects (env : natStructure.Assignment)
    (h : diagCoding.Reflects ()) :
    natStructure.evalFormula env (diagCoding.godel ()) = half :=
  diagCoding.godel_eval_half_of_reflects () h env

/-- The crisp Tarski-Goedel obstruction realised concretely: no provability
    interpretation on this structure that reflects the Goedel sentence at its
    code can be two-valued there. -/
theorem nat_no_crisp_godel (env : natStructure.Assignment)
    (hrefl : natStructure.pred ()
        [natStructure.evalTerm env (diagCoding.code (diagCoding.godel ()))] =
      natStructure.evalFormula env (diagCoding.godel ()))
    (hcrisp : natStructure.pred ()
        [natStructure.evalTerm env (diagCoding.code (diagCoding.godel ()))] = 0 ∨
      natStructure.pred ()
        [natStructure.evalTerm env (diagCoding.code (diagCoding.godel ()))] = 1) :
    False :=
  diagCoding.no_crisp_godel () env hrefl hcrisp

end natCoding

end Foundation
end Cred
