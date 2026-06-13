/-
  Cred Foundation Interface

  The exported foundation layer. A single `CredFoundation` bundle names the
  pieces a downstream development consumes: the value carrier with the product
  De Morgan triplet (`neg`/`conj`/`disj`), the threshold and certainty
  consequence relations over the first-order language, the crisp-equality and
  quantifier law interfaces a structure may satisfy, and the conditioning fiber
  `Cond` (the admissible solution set of the chain rule).

  This is a thin export over the existing modules: every field points at an
  already-proved definition, and the accessor lemmas just unfold the native
  wiring so a downstream file can use the layer without reaching into
  internals. It records, in one place, what the foundation layer offers; it is
  NOT a replacement for ZFC or the Lean kernel. Higher Lean layers recover
  classical reasoning on top of it.

  There is deliberately no internal implication or conditional constructor:
  dependence is carried by the conditioning fiber `cond`, not by a Formula
  arrow.
-/

import Cred.Foundation.Calculus
import Cred.Cond.Admissible

namespace Cred
namespace Foundation

universe u v w s

open Credence

/-- The foundation layer bundle.

The carrier `Value` comes with the three core operations of the product De
Morgan triplet and an order. `threshold`/`certainty` are the semantic
consequence relations over the first-order language at a fixed value type for
the predicates; `crispEquality`/`quantifier` are the law interfaces a structure
may satisfy; and `cond` is the conditioning fiber, the admissible set of
conditional values solving the chain rule `c ⊗ e = j`. Higher developments
program against these fields rather than the underlying modules. -/
structure CredFoundation (Func : Type u) (Pred : Type v) where
  /-- The value carrier. -/
  Value : Type w
  /-- Order on values. -/
  le : Value → Value → Prop
  /-- Negation (complement). -/
  neg : Value → Value
  /-- Conjunction (product). -/
  conj : Value → Value → Value
  /-- Disjunction (De Morgan dual). -/
  disj : Value → Value → Value
  /-- Threshold consequence at threshold `t`. -/
  threshold : Value → List (Formula Func Pred) → Formula Func Pred → Prop
  /-- Certainty consequence. -/
  certainty : List (Formula Func Pred) → Formula Func Pred → Prop
  /-- Crisp-equality law interface for a structure. -/
  crispEquality : Structure.{u, v, s} Func Pred → Prop
  /-- Quantifier law interface for a structure. -/
  quantifier : Structure.{u, v, s} Func Pred → Prop
  /-- The conditioning fiber: admissible conditional values for joint `j`,
      evidence `e`. -/
  cond : Value → Value → Set Value

/-- The native foundation layer over `Credence`, wiring the existing
    definitions: the product De Morgan triplet, the threshold and certainty
    consequence relations, the crisp-equality and quantifier law structures,
    and the admissible-set conditioning fiber `Credence.Cond`. -/
def nativeFoundation (Func : Type u) (Pred : Type v) :
    CredFoundation.{u, v, 0, s} Func Pred where
  Value := Credence
  le := fun c₁ c₂ => c₁ ≤ c₂
  neg := Credence.neg
  conj := Credence.conj
  disj := Credence.disj
  threshold := Structure.ThresholdConsequence.{u, v, s}
  certainty := Structure.CertaintyConsequence.{u, v, s}
  crispEquality := fun M => M.CrispEquality
  quantifier := fun M => M.QuantifierLaws
  cond := Credence.Cond

/-! ## Accessor lemmas

These unfold the native wiring. A downstream file imports only this module and
this layer object, then rewrites through these lemmas to recover the concrete
definitions. -/

variable {Func : Type u} {Pred : Type v}

@[simp] theorem foundation_value :
    (nativeFoundation.{u, v, s} Func Pred).Value = Credence := rfl

@[simp] theorem foundation_le (c₁ c₂ : Credence) :
    (nativeFoundation.{u, v, s} Func Pred).le c₁ c₂ = (c₁ ≤ c₂) := rfl

@[simp] theorem foundation_neg (c : Credence) :
    (nativeFoundation.{u, v, s} Func Pred).neg c = ~c := rfl

@[simp] theorem foundation_conj (c₁ c₂ : Credence) :
    (nativeFoundation.{u, v, s} Func Pred).conj c₁ c₂ = c₁ ⊗ c₂ := rfl

@[simp] theorem foundation_disj (c₁ c₂ : Credence) :
    (nativeFoundation.{u, v, s} Func Pred).disj c₁ c₂ = c₁ ⊔ c₂ := rfl

@[simp] theorem foundation_threshold (t : Credence)
    (Γ : List (Formula Func Pred)) (φ : Formula Func Pred) :
    (nativeFoundation.{u, v, s} Func Pred).threshold t Γ φ =
      Structure.ThresholdConsequence.{u, v, s} t Γ φ := rfl

@[simp] theorem foundation_certainty
    (Γ : List (Formula Func Pred)) (φ : Formula Func Pred) :
    (nativeFoundation.{u, v, s} Func Pred).certainty Γ φ =
      Structure.CertaintyConsequence.{u, v, s} Γ φ := rfl

@[simp] theorem foundation_crispEquality (M : Structure.{u, v, s} Func Pred) :
    (nativeFoundation.{u, v, s} Func Pred).crispEquality M = M.CrispEquality :=
  rfl

@[simp] theorem foundation_quantifier (M : Structure.{u, v, s} Func Pred) :
    (nativeFoundation.{u, v, s} Func Pred).quantifier M = M.QuantifierLaws :=
  rfl

@[simp] theorem foundation_cond (j e : Credence) :
    (nativeFoundation.{u, v, s} Func Pred).cond j e = Credence.Cond j e := rfl

/-! ## Layer facts re-exported through the native bundle

The structural rules and the non-explosion shape of the conditioning fiber hold
when phrased through the layer, so a downstream file gets them without naming
the underlying modules. -/

/-- Threshold reflexivity stated through the layer. -/
theorem foundation_threshold_refl (t : Credence) (φ : Formula Func Pred) :
    (nativeFoundation.{u, v, s} Func Pred).threshold t [φ] φ :=
  Structure.threshold_reflexivity t φ

/-- Threshold cut stated through the layer. -/
theorem foundation_threshold_cut (t : Credence)
    {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred}
    (h1 : (nativeFoundation.{u, v, s} Func Pred).threshold t Γ φ)
    (h2 : (nativeFoundation.{u, v, s} Func Pred).threshold t (φ :: Γ) ψ) :
    (nativeFoundation.{u, v, s} Func Pred).threshold t Γ ψ :=
  Structure.threshold_cut t h1 h2

/-- Certainty reflexivity stated through the layer. -/
theorem foundation_certainty_refl (φ : Formula Func Pred) :
    (nativeFoundation.{u, v, s} Func Pred).certainty [φ] φ :=
  Structure.certainty_reflexivity φ

/-- The conditioning fiber at zero evidence and zero joint is the whole value
    space: impossible evidence imposes no constraint, so there is no explosion
    at the foundation layer. -/
theorem foundation_cond_zero_zero :
    (nativeFoundation.{u, v, s} Func Pred).cond (0 : Credence) (0 : Credence) =
      Set.univ :=
  Credence.cond_zero_zero_univ

/-- Membership in the conditioning fiber is exactly carrying a chain-rule
    witness, restated through the layer. -/
theorem foundation_mem_cond_iff (c j e : Credence) :
    c ∈ (nativeFoundation.{u, v, s} Func Pred).cond j e ↔
      ∃ cond : Credence.Conditioning j e, cond.condCred = c :=
  Credence.mem_cond_iff c j e

end Foundation
end Cred
