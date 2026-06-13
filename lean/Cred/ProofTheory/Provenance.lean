/-
  Cred ProofTheory: Proof Provenance (issues #634(3), #640)

  Proof objects carry NAMED assumptions.  `usedAssumptions` collects exactly
  the names that occur at the leaves of a proof.  Provenance soundness states
  that a proof from a named context `Γ` only ever uses names declared in `Γ`,
  and that the conclusion is designated by every valuation designating the used
  assumptions.

  The contrast between semantic entailment and proof-use is made explicit: a
  `theorem` node (an axiom-like leaf justified at the calculus level) carries an
  EMPTY used-assumption set, even though, semantically, any premise entails it.
-/

import Cred.ProofTheory.Generative

namespace Cred.ProofTheory

open Cred

variable {α : Type*}

/-- A named assumption: a name (`Nat`) together with the labelled formula it
    stands for. -/
structure NamedAssumption (α : Type*) where
  name : Nat
  item : LForm α

/-- A named context. -/
abbrev NamedContext (α : Type*) := List (NamedAssumption α)

/-- The labelled-formula context underlying a named context. -/
def NamedContext.items (Γ : NamedContext α) : List (LForm α) :=
  Γ.map (·.item)

/-- The set of declared names in a named context. -/
def NamedContext.names (Γ : NamedContext α) : Finset Nat :=
  (Γ.map (·.name)).toFinset

/-! ## Proof Objects

A proof object records its structure explicitly so that provenance can be read
off syntactically.  Only two leaf forms exist:

* `useAssumption n` — a leaf justified by the named assumption `n`; it counts
  toward the used-assumption set.
* `theoremNode` — a leaf justified at the calculus level (a derivable fact that
  needs no assumption); it uses NO assumption.

Internal nodes mirror the generative rules that combine subproofs. -/

inductive Proof (α : Type*) where
  /-- Leaf justified by a declared named assumption. -/
  | useAssumption : Nat → LForm α → Proof α
  /-- Leaf justified at the calculus level; uses no assumption. -/
  | theoremNode : Label → Formula α → Proof α
  /-- Conjunction-elimination-left step. -/
  | conjElimLeft : Proof α → Proof α
  /-- Conjunction-elimination-right step. -/
  | conjElimRight : Proof α → Proof α
  /-- Disjunction-introduction-left step. -/
  | disjIntroLeft : Formula α → Proof α → Proof α
  /-- Disjunction-introduction-right step. -/
  | disjIntroRight : Formula α → Proof α → Proof α

/-- The named assumptions actually used at the leaves of a proof. -/
def usedAssumptions : Proof α → Finset Nat
  | .useAssumption n _ => {n}
  | .theoremNode _ _ => ∅
  | .conjElimLeft p => usedAssumptions p
  | .conjElimRight p => usedAssumptions p
  | .disjIntroLeft _ p => usedAssumptions p
  | .disjIntroRight _ p => usedAssumptions p

/-! ## Proof checking against a named context

`Checks Γ p k φ` says that proof `p` is a valid derivation of `φ` at level `k`
from the named context `Γ`.  Theorem nodes need no assumption; assumption
leaves must be declared in `Γ`. -/

inductive Checks : NamedContext α → Proof α → Label → Formula α → Prop where
  | useAssumption {Γ : NamedContext α} {n : Nat} {k : Label} {φ : Formula α} :
      ⟨n, ⟨k, φ⟩⟩ ∈ Γ → Checks Γ (.useAssumption n ⟨k, φ⟩) k φ
  | theoremNode {Γ : NamedContext α} {k : Label} {φ : Formula α} :
      Derives [] k φ → Checks Γ (.theoremNode k φ) k φ
  | conjElimLeft {Γ : NamedContext α} {t : Credence} {φ ψ : Formula α}
      {p : Proof α} :
      Checks Γ p (.threshold t) (.conj φ ψ) →
      Checks Γ (.conjElimLeft p) (.threshold t) φ
  | conjElimRight {Γ : NamedContext α} {t : Credence} {φ ψ : Formula α}
      {p : Proof α} :
      Checks Γ p (.threshold t) (.conj φ ψ) →
      Checks Γ (.conjElimRight p) (.threshold t) ψ
  | disjIntroLeft {Γ : NamedContext α} {t : Credence} {φ ψ : Formula α}
      {p : Proof α} :
      Checks Γ p (.threshold t) φ →
      Checks Γ (.disjIntroLeft ψ p) (.threshold t) (.disj φ ψ)
  | disjIntroRight {Γ : NamedContext α} {t : Credence} {φ ψ : Formula α}
      {p : Proof α} :
      Checks Γ p (.threshold t) ψ →
      Checks Γ (.disjIntroRight φ p) (.threshold t) (.disj φ ψ)

/-! ## Provenance soundness -/

/-- Provenance containment: a checked proof only uses names declared in its
    context.  This is the syntactic provenance guarantee. -/
theorem provenance_sound {Γ : NamedContext α} {p : Proof α} {k : Label}
    {φ : Formula α} (h : Checks Γ p k φ) :
    usedAssumptions p ⊆ Γ.names := by
  induction h with
  | useAssumption =>
      rename_i m k' φ' hmem
      intro n hn
      simp only [usedAssumptions, Finset.mem_singleton] at hn
      simp only [NamedContext.names, List.mem_toFinset, List.mem_map]
      exact ⟨⟨m, ⟨k', φ'⟩⟩, hmem, hn.symm⟩
  | theoremNode _ =>
      intro n hn; simp only [usedAssumptions, Finset.not_mem_empty] at hn
  | conjElimLeft _ ih => exact ih
  | conjElimRight _ ih => exact ih
  | disjIntroLeft _ ih => exact ih
  | disjIntroRight _ ih => exact ih

/-- A checked proof erases to a generative derivation over the underlying
    labelled context.  This links provenance to the verified calculus. -/
theorem checks_to_derives {Γ : NamedContext α} {p : Proof α} {k : Label}
    {φ : Formula α} (h : Checks Γ p k φ) :
    Derives Γ.items k φ := by
  induction h with
  | useAssumption hmem =>
      apply Derives.hyp
      simp only [NamedContext.items, List.mem_map]
      exact ⟨_, hmem, rfl⟩
  | theoremNode hder =>
      exact Derives.weaken hder (by intro b hb; cases hb)
  | conjElimLeft _ ih => exact Derives.conjElimLeft ih
  | conjElimRight _ ih => exact Derives.conjElimRight ih
  | disjIntroLeft _ ih => exact Derives.disjIntroLeft ih
  | disjIntroRight _ ih => exact Derives.disjIntroRight ih

/-- Semantic soundness through provenance: a checked proof's conclusion is
    designated by every valuation that designates the used context. -/
theorem checks_semantic_sound {Γ : NamedContext α} {p : Proof α} {k : Label}
    {φ : Formula α} (h : Checks Γ p k φ) :
    ∀ v : α → Credence, Designated v Γ.items → k.designates (eval v φ) :=
  generative_sound (checks_to_derives h)

/-! ## Entailment versus proof-use

A theorem node uses no assumption.  Yet, semantically, any premise `A` entails
that same conclusion `B` whenever `B` is itself valid (it is designated under
every valuation, so trivially under those designating `A`).  This separates
"semantically entailed by `A`" from "uses `A` in the proof". -/

/-- A proof whose conclusion is a valid disjunction-with-its-negation theorem,
    built as a `theoremNode`, uses no assumption. -/
theorem theoremNode_uses_nothing (k : Label) (φ : Formula α) :
    usedAssumptions (Proof.theoremNode k φ) = (∅ : Finset Nat) := rfl

end Cred.ProofTheory
