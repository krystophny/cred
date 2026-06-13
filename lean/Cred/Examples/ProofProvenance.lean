/-
  Cred Examples: Proof Provenance (issues #634(3), #640)

  Worked toy proofs over `Fin 3` atoms.  We compute `usedAssumptions` on a
  concrete proof and separate semantic entailment from proof-use: a valid
  conclusion built as a `theoremNode` uses no assumption, yet any premise
  entails it semantically.
-/

import Cred.ProofTheory.Provenance

namespace Cred.Examples.ProofProvenance

open Cred Cred.ProofTheory

/-- Three named atoms `A, B, C`. -/
abbrev A : Formula (Fin 3) := .atom 0
abbrev B : Formula (Fin 3) := .atom 1
abbrev C : Formula (Fin 3) := .atom 2

/-- The threshold used throughout: `1/2`, inside the excluded-middle window. -/
noncomputable def t₀ : Credence := Credence.half

/-- Named context: assumption `7` is the conjunction `A ∧ B` at threshold `t₀`. -/
noncomputable def Γ₀ : NamedContext (Fin 3) :=
  [ ⟨7, ⟨.threshold t₀, .conj A B⟩⟩ ]

/-- A worked proof: from the named conjunction `A ∧ B`, derive `A` by
    conjunction elimination.  It uses exactly assumption `7`. -/
noncomputable def proofA : Proof (Fin 3) :=
  .conjElimLeft (.useAssumption 7 ⟨.threshold t₀, .conj A B⟩)

/-- The worked proof checks: it derives `A` at threshold `t₀` from `Γ₀`. -/
theorem proofA_checks : Checks Γ₀ proofA (.threshold t₀) A := by
  apply Checks.conjElimLeft (ψ := B)
  apply Checks.useAssumption
  simp [Γ₀]

/-- The computed used-assumption set of the worked proof is exactly `{7}`. -/
theorem used_assumptions_example :
    usedAssumptions proofA = ({7} : Finset Nat) := rfl

/-- Provenance containment holds for the worked proof: it uses only declared
    names. -/
theorem proofA_provenance : usedAssumptions proofA ⊆ Γ₀.names :=
  provenance_sound proofA_checks

/-! ## Entailment versus proof-use

`B ⊔ ~B` is valid at threshold `t₀ = 1/2` (excluded middle holds up to `3/4`),
so it is derivable from no premises via the `excludedMiddle` axiom schema and
introduced as a `theoremNode` that uses no assumption.  Yet, semantically, the
premise `A` entails it: every valuation designating `A` also designates
`B ⊔ ~B`. -/

/-- The excluded-middle disjunction `B ⊔ ~B` as a toy formula. -/
def emB : Formula (Fin 3) := .disj B (.neg B)

/-- `B ⊔ ~B` is derivable from no premises at threshold `t₀`. -/
theorem emB_derives :
    Derives ([] : List (LForm (Fin 3))) (.threshold t₀) emB := by
  apply Derives.excludedMiddle
  simp only [t₀, Credence.half_val]; norm_num

/-- The theorem-node proof of `B ⊔ ~B`. -/
noncomputable def proofEM : Proof (Fin 3) :=
  .theoremNode (.threshold t₀) emB

/-- The theorem-node proof checks from any named context. -/
theorem proofEM_checks (Γ : NamedContext (Fin 3)) :
    Checks Γ proofEM (.threshold t₀) emB :=
  Checks.theoremNode emB_derives

/-- The theorem-node proof uses NO assumption. -/
theorem entails_but_unused :
    usedAssumptions proofEM = (∅ : Finset Nat) ∧
    ∀ v : Fin 3 → Credence,
      Label.designates (.threshold t₀) (eval v A) →
      Label.designates (.threshold t₀) (eval v emB) := by
  refine ⟨rfl, ?_⟩
  intro v _
  -- `emB` is designated under every valuation, in particular those designating `A`.
  have h := generative_sound emB_derives v (by intro b hb; cases hb)
  exact h

end Cred.Examples.ProofProvenance
