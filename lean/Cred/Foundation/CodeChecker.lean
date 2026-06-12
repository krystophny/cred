/-
  Cred Foundation CodeChecker

  The reflective loop so far runs in two halves. `Cred.SelfRep` numbers a
  `FoundationCertificateTree` injectively into `Nat` (`gnumTree`), and
  `Cred.Foundation.CheckBool` runs a computable, reals-free checker `checkBool`
  on the *tree*. `reflect_accepted_checkBool` ties them through the numbering,
  but its statement still mentions the tree on the right: the running checker
  consumes the inductive value, not the arithmetic code.

  This module closes that last gap. It builds a **computable, fuel-bounded
  decoder** that inverts the `Nat.pair` tagging of `gnum*` and recovers the
  tree from its code, and a checker `checkCode` that runs *directly on the
  code*: decode, then `checkBool`. The core coincidence
  `checkCode_gnumTree` shows that on any numbered tree (with enough fuel)
  `checkCode` equals `checkBool` on that tree, so the arithmetic checker and the
  verified real-free checker decide the same thing. Soundness rides along:
  a `true` arithmetic verdict on a code recovers the verified consequence.

  The decoder is total via fuel and inverts every `gnum*` constructor, so the
  whole `Term`/`Formula`/payload/tree numbering is decoded, nothing assumed.
  The round-trip is proved against the structural `size` of the encoded object,
  which bounds the fuel that suffices.
-/

import Cred.Foundation.Reflect

namespace Cred
namespace Foundation
namespace Structure

open Cred.SelfRep

universe u v w

variable {Func : Type u} {Pred : Type v}

/-! ## Decoding the alphabet

The numberings `gnum*` are parameterised by injective alphabet numberings
`gf : Func → Nat`, `gp : Pred → Nat`. To decode we need computable left
inverses `df : Nat → Option Func`, `dp : Nat → Option Pred` with
`df (gf f) = some f` and `dp (gp p) = some p`. At the concrete instance
`Func = Pred = Nat` with `gf = gp = id` these are just `some`. -/

/-! ## Fuel-bounded decoders

Each decoder reads the `Nat.pair` tag with `Nat.unpair` and dispatches on it,
exactly inverting the corresponding `gnum*` clause. Fuel bounds the recursion
so the definitions are structurally terminating and computable. -/

section Decode

variable (df : Nat → Option Func)

mutual

/-- Decode a term and, mutually, a term list. `n.unpair = (tag, rest)`
    inverts the `Nat.pair` tagging of `gnumTerm`/`gnumTermList`. -/
def decodeTerm : Nat → Nat → Option (Term Func)
  | 0, _ => none
  | fuel + 1, n =>
      match n.unpair.1 with
      | 0 => some (.var n.unpair.2)
      | 1 =>
          let inner := n.unpair.2
          match df inner.unpair.1 with
          | some f =>
              match decodeTermList fuel inner.unpair.2 with
              | some args => some (.app f args)
              | none => none
          | none => none
      | _ => none

/-- Decode a term list. `0` is the empty list; a cons code is `pair … … + 1`. -/
def decodeTermList : Nat → Nat → Option (List (Term Func))
  | 0, _ => none
  | fuel + 1, n =>
      match n with
      | 0 => some []
      | m + 1 =>
          match decodeTerm fuel m.unpair.1 with
          | some t =>
              match decodeTermList fuel m.unpair.2 with
              | some ts => some (t :: ts)
              | none => none
          | none => none

end

end Decode

section DecodeFormula

variable (df : Nat → Option Func) (dp : Nat → Option Pred)

mutual

/-- Decode a formula, inverting every `gnumFormula` clause. -/
def decodeFormula : Nat → Nat → Option (Formula Func Pred)
  | 0, _ => none
  | fuel + 1, n =>
      match n.unpair.1, n.unpair.2 with
      | 0, _ => some .top
      | 1, _ => some .bot
      | 2, rest =>
          match dp rest.unpair.1 with
          | some p =>
              match decodeTermList df fuel rest.unpair.2 with
              | some args => some (.atom p args)
              | none => none
          | none => none
      | 3, rest =>
          match decodeTerm df fuel rest.unpair.1 with
          | some a =>
              match decodeTerm df fuel rest.unpair.2 with
              | some b => some (.equal a b)
              | none => none
          | none => none
      | 4, rest =>
          match decodeFormula fuel rest with
          | some φ => some (.neg φ)
          | none => none
      | 5, rest =>
          match decodeFormula fuel rest.unpair.1 with
          | some φ =>
              match decodeFormula fuel rest.unpair.2 with
              | some ψ => some (.conj φ ψ)
              | none => none
          | none => none
      | 6, rest =>
          match decodeFormula fuel rest.unpair.1 with
          | some φ =>
              match decodeFormula fuel rest.unpair.2 with
              | some ψ => some (.disj φ ψ)
              | none => none
          | none => none
      | 7, rest =>
          match decodeFormula fuel rest with
          | some φ => some (.forallE φ)
          | none => none
      | 8, rest =>
          match decodeFormula fuel rest with
          | some φ => some (.existsE φ)
          | none => none
      | _, _ => none

/-- Decode a formula list. `0` is empty; a cons code is `pair … … + 1`. -/
def decodeFormulaList : Nat → Nat → Option (List (Formula Func Pred))
  | 0, _ => none
  | fuel + 1, n =>
      match n with
      | 0 => some []
      | m + 1 =>
          match decodeFormula fuel m.unpair.1 with
          | some φ =>
              match decodeFormulaList fuel m.unpair.2 with
              | some φs => some (φ :: φs)
              | none => none
          | none => none

end

end DecodeFormula

section DecodePayload

variable (df : Nat → Option Func) (dp : Nat → Option Pred)

/-- Decode a rule payload, inverting every `gnumPayload` clause. -/
def decodePayload : Nat → Nat → Option (FoundationRulePayload Func Pred)
  | 0, _ => none
  | fuel + 1, n =>
      match n.unpair.1, n.unpair.2 with
      | 0, rest =>
          match decodeFormulaList df dp fuel rest.unpair.1 with
          | some Γ =>
              match decodeFormula df dp fuel rest.unpair.2 with
              | some φ => some (.hyp Γ φ)
              | none => none
          | none => none
      | 1, rest =>
          match decodeFormulaList df dp fuel rest with
          | some Δ => some (.weaken Δ)
          | none => none
      | 2, rest =>
          match decodeFormula df dp fuel rest with
          | some mid => some (.cut mid)
          | none => none
      | 3, _ => some .conjElimLeft
      | 4, _ => some .conjElimRight
      | 5, rest =>
          match decodeFormula df dp fuel rest with
          | some ψ => some (.disjIntroLeft ψ)
          | none => none
      | 6, rest =>
          match decodeFormula df dp fuel rest with
          | some φ => some (.disjIntroRight φ)
          | none => none
      | 7, rest =>
          match decodeFormulaList df dp fuel rest.unpair.1 with
          | some Γ =>
              match decodeTerm df fuel rest.unpair.2 with
              | some τ => some (.equalityRefl Γ τ)
              | none => none
          | none => none
      | 8, _ => some .equalitySymm
      | 9, _ => some .equalityTrans
      | 10, rest =>
          match decodeTerm df fuel rest.unpair.1 with
          | some τ =>
              match decodeTerm df fuel rest.unpair.2.unpair.1 with
              | some υ =>
                  match decodeFormula df dp fuel rest.unpair.2.unpair.2 with
                  | some φ => some (.equalitySubst τ υ φ)
                  | none => none
              | none => none
          | none => none
      | 11, rest =>
          match decodeTerm df fuel rest with
          | some τ => some (.forallElim τ)
          | none => none
      | 12, rest =>
          match decodeFormula df dp fuel rest.unpair.1 with
          | some φ =>
              match decodeTerm df fuel rest.unpair.2 with
              | some τ => some (.existsIntro φ τ)
              | none => none
          | none => none
      | _, _ => none

end DecodePayload

section DecodeTree

variable (df : Nat → Option Func) (dp : Nat → Option Pred)

mutual

/-- Decode a certificate tree and, mutually, a tree list. A node pairs its
    payload code with its child-list code; a cons code is `pair … … + 1`. -/
def decodeTree : Nat → Nat → Option (FoundationCertificateTree Func Pred)
  | 0, _ => none
  | fuel + 1, n =>
      match decodePayload df dp fuel n.unpair.1 with
      | some payload =>
          match decodeTreeList fuel n.unpair.2 with
          | some children => some (.node payload children)
          | none => none
      | none => none

/-- Decode a certificate-tree list. -/
def decodeTreeList :
    Nat → Nat → Option (List (FoundationCertificateTree Func Pred))
  | 0, _ => none
  | fuel + 1, n =>
      match n with
      | 0 => some []
      | m + 1 =>
          match decodeTree fuel m.unpair.1 with
          | some t =>
              match decodeTreeList fuel m.unpair.2 with
              | some ts => some (t :: ts)
              | none => none
          | none => none

end

end DecodeTree

/-! ## Structural size

The size measures bound the fuel that suffices to decode. Every recursive
child has strictly smaller size, and every size is positive, so the cons /
node case can pass `fuel` to children after consuming one unit. -/

mutual

/-- Size of a term: one plus the size of its argument list. -/
def termSize : Term Func → Nat
  | .var _ => 1
  | .app _ args => termListSize args + 1

/-- Size of a term list. -/
def termListSize : List (Term Func) → Nat
  | [] => 1
  | t :: ts => termSize t + termListSize ts + 1

end

mutual

/-- Size of a formula. -/
def formulaSize : Formula Func Pred → Nat
  | .top => 1
  | .bot => 1
  | .atom _ args => termListSize args + 1
  | .equal a b => termSize a + termSize b + 1
  | .neg φ => formulaSize φ + 1
  | .conj φ ψ => formulaSize φ + formulaSize ψ + 1
  | .disj φ ψ => formulaSize φ + formulaSize ψ + 1
  | .forallE φ => formulaSize φ + 1
  | .existsE φ => formulaSize φ + 1

end

/-- Size of a formula list. -/
def formulaListSize : List (Formula Func Pred) → Nat
  | [] => 1
  | φ :: φs => formulaSize φ + formulaListSize φs + 1

/-- Size of a payload: one plus the size of its carried data. -/
def payloadSize : FoundationRulePayload Func Pred → Nat
  | .hyp Γ φ => formulaListSize Γ + formulaSize φ + 1
  | .weaken Δ => formulaListSize Δ + 1
  | .cut mid => formulaSize mid + 1
  | .conjElimLeft => 1
  | .conjElimRight => 1
  | .disjIntroLeft ψ => formulaSize ψ + 1
  | .disjIntroRight φ => formulaSize φ + 1
  | .equalityRefl Γ τ => formulaListSize Γ + termSize τ + 1
  | .equalitySymm => 1
  | .equalityTrans => 1
  | .equalitySubst τ υ φ => termSize τ + termSize υ + formulaSize φ + 1
  | .forallElim τ => termSize τ + 1
  | .existsIntro φ τ => formulaSize φ + termSize τ + 1

mutual

/-- Size of a certificate tree. -/
def treeSize : FoundationCertificateTree Func Pred → Nat
  | .node payload children => payloadSize payload + treeListSize children + 1

/-- Size of a certificate-tree list. -/
def treeListSize : List (FoundationCertificateTree Func Pred) → Nat
  | [] => 1
  | t :: ts => treeSize t + treeListSize ts + 1

end

/-! ## Round-trip lemmas

Each lemma says: with fuel at least the size of the object, the decoder
recovers it from its code. The fuel bound `size ≤ fuel` lets the `fuel + 1`
clause consume one unit and still cover every strictly smaller child. -/

section RoundTrip

variable {df : Nat → Option Func} {dp : Nat → Option Pred}
variable {gf : Func → Nat} {gp : Pred → Nat}
variable (hdf : ∀ f, df (gf f) = some f) (hdp : ∀ p, dp (gp p) = some p)

/-! Sizes are positive, so the `fuel = 0` branch never fires under the bound. -/

theorem termSize_pos (t : Term Func) : 1 ≤ termSize t := by
  cases t <;> simp [termSize]

theorem termListSize_pos (ts : List (Term Func)) : 1 ≤ termListSize ts := by
  cases ts <;> simp [termListSize]

theorem formulaSize_pos (φ : Formula Func Pred) : 1 ≤ formulaSize φ := by
  cases φ <;> simp [formulaSize]

theorem formulaListSize_pos (φs : List (Formula Func Pred)) :
    1 ≤ formulaListSize φs := by
  cases φs <;> simp [formulaListSize]

theorem payloadSize_pos (payload : FoundationRulePayload Func Pred) :
    1 ≤ payloadSize payload := by
  cases payload <;> simp [payloadSize]

theorem treeSize_pos (tree : FoundationCertificateTree Func Pred) :
    1 ≤ treeSize tree := by
  cases tree with
  | node payload children => simp [treeSize]

theorem treeListSize_pos (ts : List (FoundationCertificateTree Func Pred)) :
    1 ≤ treeListSize ts := by
  cases ts <;> simp [treeListSize]

section Terms
include hdf
-- The list partner of each mutual block threads `hdf`/`hdp` to its sibling but
-- never names them itself; silence the resulting unused-variable linter.
set_option linter.unusedSectionVars false

mutual

theorem decodeTerm_gnum :
    ∀ (fuel : Nat) (t : Term Func), termSize t ≤ fuel →
      decodeTerm df fuel (gnumTerm gf t) = some t
  | 0, t, h => absurd h (by have := termSize_pos t; omega)
  | fuel + 1, .var n, _ => by
      simp only [gnumTerm, decodeTerm, Nat.unpair_pair]
  | fuel + 1, .app f args, h => by
      simp only [termSize] at h
      have hargs : termListSize args ≤ fuel := by omega
      simp only [gnumTerm, decodeTerm, Nat.unpair_pair, hdf f,
        decodeTermList_gnum fuel args hargs]

theorem decodeTermList_gnum :
    ∀ (fuel : Nat) (ts : List (Term Func)), termListSize ts ≤ fuel →
      decodeTermList df fuel (gnumTermList gf ts) = some ts
  | 0, ts, h => absurd h (by have := termListSize_pos ts; omega)
  | fuel + 1, [], _ => by
      simp only [gnumTermList, decodeTermList]
  | fuel + 1, t :: ts, h => by
      simp only [termListSize] at h
      have ht : termSize t ≤ fuel := by omega
      have hts : termListSize ts ≤ fuel := by omega
      simp only [gnumTermList, decodeTermList, Nat.unpair_pair,
        decodeTerm_gnum fuel t ht, decodeTermList_gnum fuel ts hts]

end

end Terms

section FormulasTrees
include hdf hdp
set_option linter.unusedSectionVars false

mutual

theorem decodeFormula_gnum :
    ∀ (fuel : Nat) (φ : Formula Func Pred), formulaSize φ ≤ fuel →
      decodeFormula df dp fuel (gnumFormula gf gp φ) = some φ
  | 0, φ, h => absurd h (by have := formulaSize_pos φ; omega)
  | _ + 1, .top, _ => by simp only [gnumFormula, decodeFormula, Nat.unpair_pair]
  | _ + 1, .bot, _ => by simp only [gnumFormula, decodeFormula, Nat.unpair_pair]
  | fuel + 1, .atom p args, h => by
      simp only [formulaSize] at h
      have hargs : termListSize args ≤ fuel := by omega
      simp only [gnumFormula, decodeFormula, Nat.unpair_pair, hdp p,
        decodeTermList_gnum hdf fuel args hargs]
  | fuel + 1, .equal a b, h => by
      simp only [formulaSize] at h
      have ha : termSize a ≤ fuel := by omega
      have hb : termSize b ≤ fuel := by omega
      simp only [gnumFormula, decodeFormula, Nat.unpair_pair,
        decodeTerm_gnum hdf fuel a ha, decodeTerm_gnum hdf fuel b hb]
  | fuel + 1, .neg φ, h => by
      simp only [formulaSize] at h
      have hφ : formulaSize φ ≤ fuel := by omega
      simp only [gnumFormula, decodeFormula, Nat.unpair_pair,
        decodeFormula_gnum fuel φ hφ]
  | fuel + 1, .conj φ ψ, h => by
      simp only [formulaSize] at h
      have hφ : formulaSize φ ≤ fuel := by omega
      have hψ : formulaSize ψ ≤ fuel := by omega
      simp only [gnumFormula, decodeFormula, Nat.unpair_pair,
        decodeFormula_gnum fuel φ hφ, decodeFormula_gnum fuel ψ hψ]
  | fuel + 1, .disj φ ψ, h => by
      simp only [formulaSize] at h
      have hφ : formulaSize φ ≤ fuel := by omega
      have hψ : formulaSize ψ ≤ fuel := by omega
      simp only [gnumFormula, decodeFormula, Nat.unpair_pair,
        decodeFormula_gnum fuel φ hφ, decodeFormula_gnum fuel ψ hψ]
  | fuel + 1, .forallE φ, h => by
      simp only [formulaSize] at h
      have hφ : formulaSize φ ≤ fuel := by omega
      simp only [gnumFormula, decodeFormula, Nat.unpair_pair,
        decodeFormula_gnum fuel φ hφ]
  | fuel + 1, .existsE φ, h => by
      simp only [formulaSize] at h
      have hφ : formulaSize φ ≤ fuel := by omega
      simp only [gnumFormula, decodeFormula, Nat.unpair_pair,
        decodeFormula_gnum fuel φ hφ]

end

theorem decodeFormulaList_gnum :
    ∀ (fuel : Nat) (φs : List (Formula Func Pred)), formulaListSize φs ≤ fuel →
      decodeFormulaList df dp fuel (gnumFormulaList gf gp φs) = some φs
  | 0, φs, h => absurd h (by have := formulaListSize_pos φs; omega)
  | fuel + 1, [], _ => by simp only [gnumFormulaList, decodeFormulaList]
  | fuel + 1, φ :: φs, h => by
      simp only [formulaListSize] at h
      have hφ : formulaSize φ ≤ fuel := by omega
      have hφs : formulaListSize φs ≤ fuel := by omega
      simp only [gnumFormulaList, decodeFormulaList, Nat.unpair_pair,
        decodeFormula_gnum hdf hdp fuel φ hφ,
        decodeFormulaList_gnum fuel φs hφs]

theorem decodePayload_gnum :
    ∀ (fuel : Nat) (payload : FoundationRulePayload Func Pred),
      payloadSize payload ≤ fuel →
      decodePayload df dp fuel (gnumPayload gf gp payload) = some payload
  | 0, payload, h => absurd h (by have := payloadSize_pos payload; omega)
  | fuel + 1, .hyp Γ φ, h => by
      simp only [payloadSize] at h
      have hΓ : formulaListSize Γ ≤ fuel := by omega
      have hφ : formulaSize φ ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeFormulaList_gnum hdf hdp fuel Γ hΓ,
        decodeFormula_gnum hdf hdp fuel φ hφ]
  | fuel + 1, .weaken Δ, h => by
      simp only [payloadSize] at h
      have hΔ : formulaListSize Δ ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeFormulaList_gnum hdf hdp fuel Δ hΔ]
  | fuel + 1, .cut mid, h => by
      simp only [payloadSize] at h
      have hmid : formulaSize mid ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeFormula_gnum hdf hdp fuel mid hmid]
  | fuel + 1, .conjElimLeft, _ => by
      simp only [gnumPayload, decodePayload, Nat.unpair_pair]
  | fuel + 1, .conjElimRight, _ => by
      simp only [gnumPayload, decodePayload, Nat.unpair_pair]
  | fuel + 1, .disjIntroLeft ψ, h => by
      simp only [payloadSize] at h
      have hψ : formulaSize ψ ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeFormula_gnum hdf hdp fuel ψ hψ]
  | fuel + 1, .disjIntroRight φ, h => by
      simp only [payloadSize] at h
      have hφ : formulaSize φ ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeFormula_gnum hdf hdp fuel φ hφ]
  | fuel + 1, .equalityRefl Γ τ, h => by
      simp only [payloadSize] at h
      have hΓ : formulaListSize Γ ≤ fuel := by omega
      have hτ : termSize τ ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeFormulaList_gnum hdf hdp fuel Γ hΓ,
        decodeTerm_gnum hdf fuel τ hτ]
  | fuel + 1, .equalitySymm, _ => by
      simp only [gnumPayload, decodePayload, Nat.unpair_pair]
  | fuel + 1, .equalityTrans, _ => by
      simp only [gnumPayload, decodePayload, Nat.unpair_pair]
  | fuel + 1, .equalitySubst τ υ φ, h => by
      simp only [payloadSize] at h
      have hτ : termSize τ ≤ fuel := by omega
      have hυ : termSize υ ≤ fuel := by omega
      have hφ : formulaSize φ ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeTerm_gnum hdf fuel τ hτ, decodeTerm_gnum hdf fuel υ hυ,
        decodeFormula_gnum hdf hdp fuel φ hφ]
  | fuel + 1, .forallElim τ, h => by
      simp only [payloadSize] at h
      have hτ : termSize τ ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeTerm_gnum hdf fuel τ hτ]
  | fuel + 1, .existsIntro φ τ, h => by
      simp only [payloadSize] at h
      have hφ : formulaSize φ ≤ fuel := by omega
      have hτ : termSize τ ≤ fuel := by omega
      simp only [gnumPayload, decodePayload, Nat.unpair_pair,
        decodeFormula_gnum hdf hdp fuel φ hφ,
        decodeTerm_gnum hdf fuel τ hτ]

mutual

theorem decodeTree_gnum :
    ∀ (fuel : Nat) (tree : FoundationCertificateTree Func Pred),
      treeSize tree ≤ fuel →
      decodeTree df dp fuel (gnumTree gf gp tree) = some tree
  | 0, tree, h => absurd h (by have := treeSize_pos tree; omega)
  | fuel + 1, .node payload children, h => by
      simp only [treeSize] at h
      have hp : payloadSize payload ≤ fuel := by omega
      have hc : treeListSize children ≤ fuel := by omega
      simp only [gnumTree, decodeTree, Nat.unpair_pair,
        decodePayload_gnum hdf hdp fuel payload hp,
        decodeTreeList_gnum fuel children hc]

theorem decodeTreeList_gnum :
    ∀ (fuel : Nat) (ts : List (FoundationCertificateTree Func Pred)),
      treeListSize ts ≤ fuel →
      decodeTreeList df dp fuel (gnumTreeList gf gp ts) = some ts
  | 0, ts, h => absurd h (by have := treeListSize_pos ts; omega)
  | fuel + 1, [], _ => by simp only [gnumTreeList, decodeTreeList]
  | fuel + 1, t :: ts, h => by
      simp only [treeListSize] at h
      have ht : treeSize t ≤ fuel := by omega
      have hts : treeListSize ts ≤ fuel := by omega
      simp only [gnumTreeList, decodeTreeList, Nat.unpair_pair,
        decodeTree_gnum fuel t ht, decodeTreeList_gnum fuel ts hts]

end

end FormulasTrees

end RoundTrip

/-! ## The arithmetic checker

`checkCode` runs on a `Nat` code directly: decode with the supplied fuel, then
hand the recovered tree to the verified real-free `checkBool`. A failed decode
is a reject. -/

/-- The checker that runs on arithmetic codes. -/
def checkCode [DecidableEq Func] [DecidableEq Pred]
    (df : Nat → Option Func) (dp : Nat → Option Pred)
    (fuel : Nat) (n : Nat) : Bool :=
  match decodeTree df dp fuel n with
  | some tree => checkBool tree
  | none => false

/-- Core coincidence: on a numbered tree, with fuel at least its size, the
    arithmetic checker agrees with the verified real-free checker on the tree
    itself. The arithmetic representation is decided exactly as the inductive
    one. -/
theorem checkCode_gnumTree [DecidableEq Func] [DecidableEq Pred]
    {df : Nat → Option Func} {dp : Nat → Option Pred}
    {gf : Func → Nat} {gp : Pred → Nat}
    (hdf : ∀ f, df (gf f) = some f) (hdp : ∀ p, dp (gp p) = some p)
    (fuel : Nat) (tree : FoundationCertificateTree Func Pred)
    (hfuel : treeSize tree ≤ fuel) :
    checkCode df dp fuel (gnumTree gf gp tree) = checkBool tree := by
  unfold checkCode
  rw [decodeTree_gnum hdf hdp fuel tree hfuel]

/-- Coincidence with the verified checker's `isSome`: the arithmetic verdict on
    a code equals the verified checker's verdict on the numbered tree, for every
    threshold `t`. -/
theorem checkCode_gnumTree_isSome [DecidableEq Func] [DecidableEq Pred]
    {df : Nat → Option Func} {dp : Nat → Option Pred}
    {gf : Func → Nat} {gp : Pred → Nat}
    (hdf : ∀ f, df (gf f) = some f) (hdp : ∀ p, dp (gp p) = some p)
    (t : Credence) (fuel : Nat)
    (tree : FoundationCertificateTree Func Pred)
    (hfuel : treeSize tree ≤ fuel) :
    checkCode df dp fuel (gnumTree gf gp tree) =
      (checkFoundationCertificate t tree).isSome := by
  rw [checkCode_gnumTree hdf hdp fuel tree hfuel, checkBool_eq_isSome t tree]

/-- Reflective coincidence on codes: the object-level acceptance predicate
    `accepted` on a code is exactly the arithmetic checker's `true` verdict.
    This is `reflect_accepted_checkBool` transported to the running checker on
    the code. -/
theorem checkCode_gnumTree_accepted [DecidableEq Func] [DecidableEq Pred]
    {df : Nat → Option Func} {dp : Nat → Option Pred}
    {gf : Func → Nat} {gp : Pred → Nat}
    (hdf : ∀ f, df (gf f) = some f) (hdp : ∀ p, dp (gp p) = some p)
    (hgf : Function.Injective gf) (hgp : Function.Injective gp)
    (t : Credence) (fuel : Nat)
    (tree : FoundationCertificateTree Func Pred)
    (hfuel : treeSize tree ≤ fuel) :
    accepted t gf gp (gnumTree gf gp tree) ↔
      checkCode df dp fuel (gnumTree gf gp tree) = true := by
  rw [checkCode_gnumTree hdf hdp fuel tree hfuel]
  exact reflect_accepted_checkBool hgf hgp tree

/-- Soundness on codes: when the arithmetic checker accepts the code of a tree
    (with enough fuel), the verified checker produces a certificate and the
    object-level consequence holds at threshold `t`. No reals run in the
    arithmetic checker. -/
theorem checkCode_gnumTree_sound [DecidableEq Func] [DecidableEq Pred]
    {df : Nat → Option Func} {dp : Nat → Option Pred}
    {gf : Func → Nat} {gp : Pred → Nat}
    (hdf : ∀ f, df (gf f) = some f) (hdp : ∀ p, dp (gp p) = some p)
    (t : Credence) (fuel : Nat)
    (tree : FoundationCertificateTree Func Pred)
    (hfuel : treeSize tree ≤ fuel)
    (h : checkCode df dp fuel (gnumTree gf gp tree) = true) :
    ∃ checked : CheckedFoundationProof t Func Pred,
      checkFoundationCertificate t tree = some checked ∧
      FoundationThresholdConsequence.{u, v, w} t
        checked.premises checked.conclusion := by
  rw [checkCode_gnumTree hdf hdp fuel tree hfuel] at h
  exact checkBool_true_sound t tree h

/-! ## Concrete instance: `Func = Pred = Nat`, `gf = gp = id`

`id` is injective, and `df = dp = some` is the computable inverse, so the
whole pipeline reduces and `#eval` runs. -/

/-- The trivial decoder for the identity numbering on `Nat`. -/
def idDecode : Nat → Option Nat := some

theorem idDecode_id : ∀ n : Nat, idDecode (id n) = some n := fun _ => rfl

/-- The code of the concrete example tree under the identity numbering. -/
def exampleCode : Nat := gnumTree id id exampleTree

/-- The arithmetic checker accepts the code of the example tree, by computation
    alone, with fuel equal to the tree's size. -/
theorem checkCode_exampleCode :
    checkCode idDecode idDecode (treeSize exampleTree) exampleCode = true := by
  rw [exampleCode,
    checkCode_gnumTree (df := idDecode) (dp := idDecode) (gf := id) (gp := id)
      idDecode_id idDecode_id (treeSize exampleTree) exampleTree
      (Nat.le_refl _)]
  exact checkBool_exampleTree

-- Executable arithmetic verdict: the checker runs on the Goedel code of the
-- example tree and prints `true`. This is the checker operating on the
-- system's own arithmetic representation, no reals involved.
#eval checkCode idDecode idDecode (treeSize exampleTree) exampleCode
-- Round-trip at the code level: re-encoding the decoded tree returns the code.
#eval (decodeTree idDecode idDecode (treeSize exampleTree) exampleCode).map
        (gnumTree id id) == some exampleCode

/-- Soundness on the concrete code: the arithmetic `true` verdict on
    `exampleCode` recovers the verified certificate and its object-level
    consequence at threshold `1`. -/
theorem exampleCode_sound :
    ∃ checked : CheckedFoundationProof (1 : Credence) Nat Nat,
      checkFoundationCertificate (1 : Credence) exampleTree = some checked ∧
      FoundationThresholdConsequence.{0, 0, w} (1 : Credence)
        checked.premises checked.conclusion :=
  checkCode_gnumTree_sound (df := idDecode) (dp := idDecode) (gf := id) (gp := id)
    idDecode_id idDecode_id (1 : Credence) (treeSize exampleTree)
    exampleTree (Nat.le_refl _) checkCode_exampleCode

end Structure
end Foundation
end Cred
