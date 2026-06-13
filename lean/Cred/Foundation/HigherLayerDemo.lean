/-
  Cred Foundation Higher-Layer Demo

  The foundation layer (`Cred.Foundation.*`) recovers classical first-order
  reasoning -- crisp equality, quantifier instantiation, threshold consequence,
  and certificate checking -- on top of the credence algebra, with no internal
  conditional and no explosion. This file demonstrates the intended USE of that
  layer: a higher-level Lean development imports the foundation pieces and builds
  derived results by COMPOSING the foundation rules, rather than re-proving them
  from scratch or bypassing the layer.

  Nothing here is a new primitive. Every consequence below is obtained by
  chaining `FoundationProof` constructors (the foundation kernel's typed
  derivations) and then reading off semantic soundness through
  `FoundationProof.sound`. An external Lean development would proceed exactly the
  same way: `import Cred.Foundation.Calculus`, build a `FoundationProof`, call
  `.sound`. We also re-package the arithmetic sqrt(2) contradiction (the math
  benchmark layer in `Cred.Examples`) as a higher-layer fact, to show both the
  proof-theoretic and the Mathlib-backed higher layers resting on Cred modules.

  Honesty: this is a foundation LAYER that recovers classical reasoning and that
  higher Lean layers can build on. It is not a replacement for ZFC or for Lean's
  kernel; the underlying trust is still Mathlib and Lean. No unproved holes.
-/

import Cred.Foundation.Examples
import Cred.Examples.Sqrt2Branch

namespace Cred
namespace Foundation
namespace Demo

universe u v w

open Cred.Foundation.Structure

variable {Func : Type u} {Pred : Type v}

/-! ## A derived rule by composition of foundation rules

The foundation kernel ships atomic rules: `equalitySymm`, `equalityTrans`,
`equalitySubst`, `forallElim`, `cut`, weakening, and the propositional rules.
A higher layer combines them. As a representative composite, we derive a
"transport along a swapped equality" rule:

  from `υ = τ` and `φ[τ]` conclude `φ[υ]`,

i.e. equality substitution where the hypothesis is given in the *reversed*
orientation `υ = τ`. The foundation only provides `equalitySubst` for the
forward orientation `τ = υ`, so a higher layer must first flip the equality
with `equalitySymm` and then substitute. The proof is purely a composition of
two foundation-kernel constructors; we add no new rule. -/

/-- Higher-layer derived rule: transport `φ` along a *reversed* equality.

    Built by `equalitySymm` (flip `υ = τ` to `τ = υ`) followed by
    `equalitySubst`. Both are foundation-kernel constructors; this term is a
    pure composition, witnessing that the higher layer extends the foundation
    without touching its primitives. -/
def transportAlongSymm (t : Credence) (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationProof t
      [@Formula.equal Func Pred υ τ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) :=
  FoundationProof.equalitySubst
    (FoundationProof.equalitySymm
      (FoundationProof.base
        (Proof.hyp
          (List.mem_cons_self (Formula.equal υ τ)
            [Formula.instantiate τ φ]))))
    (FoundationProof.base
      (Proof.hyp
        (List.mem_cons_of_mem (Formula.equal υ τ)
          (List.mem_cons_self (Formula.instantiate τ φ) []))))

/-- Soundness of the derived rule, obtained by `FoundationProof.sound`. The
    higher layer pays no extra cost: composing kernel certificates yields a
    composite certificate, and the foundation's soundness theorem discharges it
    at the semantic level. -/
theorem transportAlongSymm_sound (t : Credence)
    (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred υ τ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) :=
  FoundationProof.sound (transportAlongSymm t τ υ φ)

/-! ## Composing a quantifier step on top of the derived rule

The higher layer keeps composing. Here we feed a universally quantified
hypothesis into the foundation's `forallElim` and then chain a `cut` with the
derived equality transport above. From

  `∀ φ` (read at instance `τ`),   `υ = τ`

we conclude `φ[υ]`: instantiate the universal at `τ` to get `φ[τ]`, then
transport along the reversed equality `υ = τ`. Every step is a foundation
constructor; the higher layer only orchestrates them. -/

/-- Higher-layer composite: from a universal `∀ φ` and a reversed equality
    `υ = τ`, derive `φ[υ]`. Uses `forallElim` (quantifier rule) and the derived
    `transportAlongSymm` (equality rules), glued with `cut` and `weaken`. -/
def forallThenTransport (t : Credence)
    (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationProof t
      [Formula.forallE φ, @Formula.equal Func Pred υ τ]
      (Formula.instantiate υ φ) :=
  let elim :
      FoundationProof t
        [Formula.forallE φ, @Formula.equal Func Pred υ τ]
        (Formula.instantiate τ φ) :=
    FoundationProof.forallElim
      (FoundationProof.base
        (Proof.hyp
          (List.mem_cons_self (Formula.forallE φ)
            [Formula.equal υ τ])))
  -- transport needs both `υ = τ` and `φ[τ]` in context; weaken it to the
  -- working context, then `cut` against the `forallElim` result.
  let transport :
      FoundationProof t
        [Formula.instantiate τ φ, Formula.forallE φ,
          @Formula.equal Func Pred υ τ]
        (Formula.instantiate υ φ) :=
    FoundationProof.weaken (transportAlongSymm t τ υ φ)
      (by
        intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
        rcases hp with h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h)
  FoundationProof.cut elim transport

/-- Soundness of the quantifier-plus-transport composite, again via
    `FoundationProof.sound`. -/
theorem forallThenTransport_sound (t : Credence)
    (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationThresholdConsequence.{u, v, w} t
      [Formula.forallE φ, @Formula.equal Func Pred υ τ]
      (Formula.instantiate υ φ) :=
  FoundationProof.sound (forallThenTransport t τ υ φ)

/-! ## The arithmetic higher layer

The sqrt(2) contradiction in `Cred.Examples.Sqrt2Branch` is a Mathlib-backed
benchmark resting on the `Cred.Math` parity/divisibility steps. A higher layer
consumes it directly; we re-export it here as a single named higher-layer fact
to show the math benchmark and the proof-theoretic foundation living side by
side on top of Cred modules. -/

/-- Higher-layer use of the arithmetic benchmark: the sqrt(2) descent has no
    coprime witness. Delegates to `Cred.Examples.Sqrt2Branch`. -/
theorem sqrt2_no_witness (p q : ℕ)
    (hco : Nat.Coprime p q) (h : p * p = 2 * (q * q)) (hq : q ≠ 0) : False :=
  Cred.Examples.Sqrt2Branch.sqrt2_core_contradiction p q hco h hq

/-! ## Anchor: the higher layer builds on the foundation

`higher_layer_builds_on_foundation` records, in one statement, that a higher
layer obtains a derived classical consequence purely by composing foundation
rules. The proof is the derived `transportAlongSymm_sound`, whose own proof is a
`FoundationProof.sound` over a composite of `equalitySymm` and `equalitySubst`.
There is no appeal to a new axiom or a bypass of the layer. An external Lean
project would write exactly this: import `Cred.Foundation`, assemble a
`FoundationProof`, and conclude with `.sound`. -/
theorem higher_layer_builds_on_foundation (t : Credence)
    (τ υ : Term Func) (φ : Formula Func Pred) :
    FoundationThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred υ τ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) :=
  transportAlongSymm_sound t τ υ φ

end Demo
end Foundation
end Cred
