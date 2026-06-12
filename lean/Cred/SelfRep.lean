/-
  Cred SelfRep

  Object-level (Goedel-numbered) self-representation of the foundation
  checker's proof objects.  A `FoundationCertificateTree` is the data the
  checker consumes; here that data is encoded injectively into `Nat` with
  per-constructor `Nat.pair` tags, mirroring the numbering pattern of
  `Foundation.CodingNat`.  Acceptance is then phrased as an object-level
  predicate over codes, and a faithfulness lemma ties it back to the kernel
  checker through injectivity.

  The numbering is parameterised by injective numberings of the function and
  predicate alphabets (`gf`, `gp`), because a certificate tree may carry
  arbitrary `Formula`/`Term` data over those alphabets.
-/

import Cred.Foundation.Checker
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Function.Basic

namespace Cred
namespace SelfRep

open Cred.Foundation
open Cred.Foundation.Structure

universe u v

variable {Func : Type u} {Pred : Type v}

/-! ## Numbering the object-language data carried by certificates

`gf : Func → Nat` and `gp : Pred → Nat` are injective numberings of the
alphabets.  All numberings below are injective relative to these. -/

section Coding

variable (gf : Func → Nat)

mutual

/-- Injective Goedel numbering of terms over `gf`. -/
def gnumTerm : Term Func → Nat
  | .var n => Nat.pair 0 n
  | .app f args => Nat.pair 1 (Nat.pair (gf f) (gnumTermList args))

/-- Injective numbering of term lists (`0` is the empty list). -/
def gnumTermList : List (Term Func) → Nat
  | [] => 0
  | t :: ts => Nat.pair (gnumTerm t) (gnumTermList ts) + 1

end

end Coding

mutual

theorem gnumTerm_injective {gf : Func → Nat} (hf : Function.Injective gf) :
    ∀ {s t : Term Func}, gnumTerm gf s = gnumTerm gf t → s = t
  | .var m, .var n, h => by
      simp only [gnumTerm, Nat.pair_eq_pair] at h; exact h.2 ▸ rfl
  | .var _, .app _ _, h => by simp [gnumTerm, Nat.pair_eq_pair] at h
  | .app _ _, .var _, h => by simp [gnumTerm, Nat.pair_eq_pair] at h
  | .app f args, .app g args', h => by
      simp only [gnumTerm, Nat.pair_eq_pair] at h
      obtain ⟨hfg, hargs⟩ := h.2
      rw [hf hfg, gnumTermList_injective hf hargs]

theorem gnumTermList_injective {gf : Func → Nat} (hf : Function.Injective gf) :
    ∀ {ss ts : List (Term Func)}, gnumTermList gf ss = gnumTermList gf ts → ss = ts
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [gnumTermList] at h
  | _ :: _, [], h => by simp [gnumTermList] at h
  | s :: ss, t :: ts, h => by
      simp only [gnumTermList, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
      rw [gnumTerm_injective hf h.1, gnumTermList_injective hf h.2]

end

section Coding

variable (gf : Func → Nat) (gp : Pred → Nat)

/-- Injective Goedel numbering of formulas over `gf`, `gp`. -/
def gnumFormula : Formula Func Pred → Nat
  | .top => Nat.pair 0 0
  | .bot => Nat.pair 1 0
  | .atom p args => Nat.pair 2 (Nat.pair (gp p) (gnumTermList gf args))
  | .equal a b => Nat.pair 3 (Nat.pair (gnumTerm gf a) (gnumTerm gf b))
  | .neg φ => Nat.pair 4 (gnumFormula φ)
  | .conj φ ψ => Nat.pair 5 (Nat.pair (gnumFormula φ) (gnumFormula ψ))
  | .disj φ ψ => Nat.pair 6 (Nat.pair (gnumFormula φ) (gnumFormula ψ))
  | .forallE φ => Nat.pair 7 (gnumFormula φ)
  | .existsE φ => Nat.pair 8 (gnumFormula φ)

/-- Injective numbering of formula lists (`0` is the empty list). -/
def gnumFormulaList : List (Formula Func Pred) → Nat
  | [] => 0
  | φ :: φs => Nat.pair (gnumFormula gf gp φ) (gnumFormulaList φs) + 1

end Coding

theorem gnumFormula_injective {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp) :
    Function.Injective (gnumFormula gf gp) := by
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
        | (obtain ⟨hpp, hargs⟩ := h.2;
            rw [hp hpp, gnumTermList_injective hf hargs])
  | equal a b =>
      intro ψ h
      cases ψ <;> simp only [gnumFormula, Nat.pair_eq_pair] at h <;>
        first
        | (exfalso; omega)
        | (obtain ⟨ha, hb⟩ := h.2;
            rw [gnumTerm_injective hf ha, gnumTerm_injective hf hb])
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

theorem gnumFormulaList_injective {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp) :
    ∀ {φs ψs : List (Formula Func Pred)},
      gnumFormulaList gf gp φs = gnumFormulaList gf gp ψs → φs = ψs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [gnumFormulaList] at h
  | _ :: _, [], h => by simp [gnumFormulaList] at h
  | φ :: φs, ψ :: ψs, h => by
      simp only [gnumFormulaList, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
      rw [gnumFormula_injective hf hp h.1, gnumFormulaList_injective hf hp h.2]

/-! ## Numbering rule payloads

Each payload constructor gets a distinct tag.  Constructor arguments are
encoded with the term/formula numberings; nullary fields use tag `0`. -/

section Coding

variable (gf : Func → Nat) (gp : Pred → Nat)

/-- Injective Goedel numbering of rule payloads. -/
def gnumPayload : FoundationRulePayload Func Pred → Nat
  | .hyp Γ φ => Nat.pair 0 (Nat.pair (gnumFormulaList gf gp Γ) (gnumFormula gf gp φ))
  | .weaken Δ => Nat.pair 1 (gnumFormulaList gf gp Δ)
  | .cut mid => Nat.pair 2 (gnumFormula gf gp mid)
  | .conjElimLeft => Nat.pair 3 0
  | .conjElimRight => Nat.pair 4 0
  | .disjIntroLeft ψ => Nat.pair 5 (gnumFormula gf gp ψ)
  | .disjIntroRight φ => Nat.pair 6 (gnumFormula gf gp φ)
  | .equalityRefl Γ τ => Nat.pair 7 (Nat.pair (gnumFormulaList gf gp Γ) (gnumTerm gf τ))
  | .equalitySymm => Nat.pair 8 0
  | .equalityTrans => Nat.pair 9 0
  | .equalitySubst τ υ φ =>
      Nat.pair 10 (Nat.pair (gnumTerm gf τ) (Nat.pair (gnumTerm gf υ) (gnumFormula gf gp φ)))
  | .forallElim τ => Nat.pair 11 (gnumTerm gf τ)
  | .existsIntro φ τ => Nat.pair 12 (Nat.pair (gnumFormula gf gp φ) (gnumTerm gf τ))

end Coding

theorem gnumPayload_injective {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp) :
    Function.Injective (gnumPayload gf gp) := by
  intro a b h
  cases a <;> cases b <;>
    simp only [gnumPayload, Nat.pair_eq_pair] at h <;>
    first
    | rfl
    | (exfalso; omega)
    | (obtain ⟨hl, hr⟩ := h.2;
        first
        | rw [gnumFormulaList_injective hf hp hl, gnumFormula_injective hf hp hr]
        | rw [gnumFormula_injective hf hp hl, gnumTerm_injective hf hr]
        | rw [gnumFormulaList_injective hf hp hl, gnumTerm_injective hf hr]
        | (obtain ⟨hm, hn⟩ := hr;
            rw [gnumTerm_injective hf hl, gnumTerm_injective hf hm,
              gnumFormula_injective hf hp hn]))
    | rw [gnumFormulaList_injective hf hp h.2]
    | rw [gnumFormula_injective hf hp h.2]
    | rw [gnumTerm_injective hf h.2]

/-! ## Numbering certificate trees

A node pairs its payload code with the code of its child list.  The tag `+1`
on the cons case keeps lists disjoint from the empty list code `0`. -/

section Coding

variable (gf : Func → Nat) (gp : Pred → Nat)

mutual

/-- Injective Goedel numbering of certificate trees. -/
def gnumTree : FoundationCertificateTree Func Pred → Nat
  | .node payload children =>
      Nat.pair (gnumPayload gf gp payload) (gnumTreeList children)

/-- Injective numbering of certificate-tree lists. -/
def gnumTreeList : List (FoundationCertificateTree Func Pred) → Nat
  | [] => 0
  | t :: ts => Nat.pair (gnumTree t) (gnumTreeList ts) + 1

end

end Coding

mutual

theorem gnumTree_injective {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp) :
    ∀ {s t : FoundationCertificateTree Func Pred},
      gnumTree gf gp s = gnumTree gf gp t → s = t
  | .node p cs, .node q ds, h => by
      simp only [gnumTree, Nat.pair_eq_pair] at h
      rw [gnumPayload_injective hf hp h.1, gnumTreeList_injective hf hp h.2]

theorem gnumTreeList_injective {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp) :
    ∀ {ss ts : List (FoundationCertificateTree Func Pred)},
      gnumTreeList gf gp ss = gnumTreeList gf gp ts → ss = ts
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [gnumTreeList] at h
  | _ :: _, [], h => by simp [gnumTreeList] at h
  | s :: ss, t :: ts, h => by
      simp only [gnumTreeList, Nat.add_right_cancel_iff, Nat.pair_eq_pair] at h
      rw [gnumTree_injective hf hp h.1, gnumTreeList_injective hf hp h.2]

end

theorem gnumTree_injective' {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp) :
    Function.Injective (gnumTree gf gp) :=
  fun _ _ h => gnumTree_injective hf hp h

/-! ## Object-level acceptance

The checker runs at a fixed credence threshold `t`.  `accepted t … n` says: the
code `n` is the number of some certificate tree that the kernel checker accepts
(returns `some`).  This is acceptance phrased over `Nat` codes, not over the
inductive tree directly. -/

/-- A code `n` is accepted when it numbers a tree the checker validates. -/
def accepted [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (gf : Func → Nat) (gp : Pred → Nat) (n : Nat) : Prop :=
  ∃ tree : FoundationCertificateTree Func Pred,
    gnumTree gf gp tree = n ∧
      (checkFoundationCertificate t tree).isSome = true

/-- Numbering an accepted tree yields an accepted code. -/
theorem accepted_gnum_of_check
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {gf : Func → Nat} {gp : Pred → Nat}
    {tree : FoundationCertificateTree Func Pred}
    (h : (checkFoundationCertificate t tree).isSome = true) :
    accepted t gf gp (gnumTree gf gp tree) :=
  ⟨tree, rfl, h⟩

/-- Faithfulness: under injective alphabet numberings, the object-level
    acceptance of a tree's code is equivalent to the kernel checker accepting
    that very tree.  Injectivity rules out a *different* tree sharing the code
    and sneaking acceptance in. -/
theorem accepted_gnum_iff
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {gf : Func → Nat} {gp : Pred → Nat}
    (hf : Function.Injective gf) (hp : Function.Injective gp)
    (tree : FoundationCertificateTree Func Pred) :
    accepted t gf gp (gnumTree gf gp tree) ↔
      (checkFoundationCertificate t tree).isSome = true := by
  constructor
  · rintro ⟨tree', hcode, hchk⟩
    rw [gnumTree_injective' hf hp hcode] at hchk
    exact hchk
  · intro h
    exact accepted_gnum_of_check h

end SelfRep
end Cred
