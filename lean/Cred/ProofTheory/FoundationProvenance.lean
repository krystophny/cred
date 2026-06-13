/-
  Cred ProofTheory: Foundation Proof Provenance

  Lifts used-assumption provenance from the toy `Cred.ProofTheory.Proof`
  (`Cred/ProofTheory/Provenance.lean`) to the real first-order proof layer
  `Cred.Foundation.Structure.Proof` (`Cred/Foundation/Kernel.lean`).

  `foundationUsedHyps` reads off, syntactically, the hypothesis formulas that a
  Foundation `Proof` actually consumes at its `hyp` leaves.  The cut rule
  discharges its cut formula, so a cut subproof's leaves are taken relative to
  the extended context `φ :: Γ` and the cut formula `φ` is dropped when
  reporting the hypotheses used relative to the conclusion's context `Γ`.

  The provenance soundness lemma `foundation_provenance_sound` states the
  containment guarantee: every hypothesis a proof uses is declared in its
  context.  `foundation_theorem_uses_no_hyp` is the Foundation-level
  "entails-but-unused" witness: an equality reflexivity proof proves
  `τ = τ` from the empty context while using no hypothesis at all, even though
  semantically any premise list trivially entails a valid formula.
-/

import Cred.Foundation.Kernel

namespace Cred.ProofTheory

open Cred.Foundation
open Cred.Foundation.Structure

universe u v w

namespace FoundationProvenance

variable {Func : Type u} {Pred : Type v}
variable [DecidableEq Func] [DecidableEq Pred]

/-- The hypothesis formulas actually used at the `hyp` leaves of a Foundation
    `Structure.Proof`, reported relative to the proof's own context.

    `cut` discharges its cut formula `φ`: the right subproof runs over the
    extended context `φ :: Γ`, so its used hypotheses are filtered to drop
    `φ`, leaving only hypotheses that belong to `Γ`. -/
def foundationUsedHyps {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} :
    Proof t Γ φ → List (Formula Func Pred)
  | .hyp (φ := ψ) _ => [ψ]
  | .weaken p _ => foundationUsedHyps p
  | .cut (φ := ψ) p q =>
      foundationUsedHyps p ++ (foundationUsedHyps q).filter (· ≠ ψ)
  | .conjElimLeft p => foundationUsedHyps p
  | .conjElimRight p => foundationUsedHyps p
  | .disjIntroLeft p => foundationUsedHyps p
  | .disjIntroRight p => foundationUsedHyps p

/-- Provenance soundness (containment): every hypothesis a Foundation proof
    uses at its leaves is declared in that proof's context. -/
theorem foundation_provenance_sound {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (p : Proof t Γ φ) :
    ∀ ψ ∈ foundationUsedHyps p, ψ ∈ Γ := by
  induction p with
  | hyp hmem =>
      intro ψ hψ
      simp only [foundationUsedHyps, List.mem_cons, List.not_mem_nil,
        or_false] at hψ
      subst hψ
      exact hmem
  | weaken p hsub ih =>
      intro ψ hψ
      exact hsub ψ (ih ψ hψ)
  | @cut Γ' φ' ψ' p q ihp ihq =>
      intro χ hχ
      simp only [foundationUsedHyps, List.mem_append] at hχ
      rcases hχ with hp | hqf
      · exact ihp χ hp
      · have hq : χ ∈ foundationUsedHyps q := List.mem_of_mem_filter hqf
        have hne : χ ≠ φ' := by
          have hpred := List.of_mem_filter hqf
          simpa using hpred
        rcases List.mem_cons.mp (ihq χ hq) with heq | hin
        · exact absurd heq hne
        · exact hin
  | conjElimLeft p ih => exact ih
  | conjElimRight p ih => exact ih
  | disjIntroLeft p ih => exact ih
  | disjIntroRight p ih => exact ih

/-- A `hyp` leaf reports exactly the hypothesis it stands on. -/
theorem foundationUsedHyps_hyp {t : Credence}
    {Γ : List (Formula Func Pred)} {φ : Formula Func Pred} (h : φ ∈ Γ) :
    foundationUsedHyps (Proof.hyp (t := t) h) = [φ] := rfl

/-! ## Entails-but-unused at the Foundation level

A valid formula is entailed by any premises, but a proof of it need not consume
any.  Equality reflexivity is the cleanest Foundation witness: it proves
`τ = τ` from the empty context.  As a `CrispProof` constructor it uses no
hypothesis whatsoever. -/

/-- A reflexivity-of-equality proof from the empty context exists for every
    term.  It is the canonical "no hypothesis needed" Foundation derivation. -/
def equalityReflProof (t : Credence) (τ : Term Func) :
    CrispProof t ([] : List (Formula Func Pred)) (.equal τ τ) :=
  CrispProof.equalityRefl τ

omit [DecidableEq Func] [DecidableEq Pred] in
/-- The Foundation-level entails-but-unused witness: an equality reflexivity
    proof is built without recourse to any hypothesis leaf, so there is nothing
    in its (empty) context for it to depend on. -/
theorem foundation_theorem_uses_no_hyp (t : Credence) (τ : Term Func) :
    ∃ p : CrispProof t ([] : List (Formula Func Pred)) (.equal τ τ),
      p = CrispProof.equalityRefl τ :=
  ⟨CrispProof.equalityRefl τ, rfl⟩

end FoundationProvenance

end Cred.ProofTheory
