/-
  Cred Extraction

  A runnable certificate checker. The foundation checker `checkFoundationCertificate`
  is a plain recursive `Option`-valued function that reduces once every type
  parameter is concrete and decidable. This module pins a concrete instance
  (`Func = Pred = Nat`, threshold `1`), wraps the checker in a `Bool`-valued
  decision, evaluates it to the accepting verdict, and ties a `true` verdict back to
  the verified soundness theorem so the verdict entails the object-level consequence.

  The threshold lives in `Credence`, whose carrier is `ℝ` (noncomputable in
  mathlib), so the Lean code generator cannot emit a standalone binary for this
  instance; the verdict here is established by kernel reduction inside a proof, which
  is unaffected by `noncomputable`. A standalone non-Lean executable is future work.
-/

import Cred.Foundation.Examples

namespace Cred
namespace Foundation
namespace Structure

universe w

/-- A concrete example tree over `Nat` term/predicate signatures: ∀-elimination on
    `forallE (equal (var 0) (var 0))`, instantiated at `var 1`. -/
def exampleTree : FoundationCertificateTree Nat Nat :=
  forallElimCertificateTree
    (@Formula.equal Nat Nat (Term.var 0) (Term.var 0))
    (Term.var 1)

/-- Runnable accept/reject wrapper: run the checker and report whether it
    produced a typed certificate. This is the executable verdict. -/
def runChecker (tree : FoundationCertificateTree Nat Nat) : Bool :=
  (checkFoundationCertificate (1 : Credence) tree).isSome

/-- The checker accepts the concrete tree: the verdict reduces to `true`.
    Reuses the existing `isSome` fact, which the checker establishes by reduction. -/
theorem runChecker_exampleTree : runChecker exampleTree = true := by
  unfold runChecker exampleTree
  exact forallElimCertificateTree_checks (1 : Credence)
    (@Formula.equal Nat Nat (Term.var 0) (Term.var 0)) (Term.var 1)

/-- Bridge: whenever the runnable wrapper accepts a concrete tree, the certificate
    it produced is sound, i.e. the checked premises entail the checked conclusion at
    threshold `1`. The extracted `true` verdict therefore witnesses a real
    object-level consequence. -/
theorem runChecker_true_sound
    {tree : FoundationCertificateTree Nat Nat}
    (h : runChecker tree = true) :
    ∃ checked : CheckedFoundationProof (1 : Credence) Nat Nat,
      checkFoundationCertificate (1 : Credence) tree = some checked ∧
      FoundationThresholdConsequence.{0, 0, w} (1 : Credence)
        checked.premises checked.conclusion := by
  unfold runChecker at h
  cases hcheck : checkFoundationCertificate (1 : Credence) tree with
  | none => rw [hcheck] at h; simp at h
  | some checked =>
      exact ⟨checked, rfl, checkFoundationCertificate_sound hcheck⟩

/-- Specialised to the example tree: the executable verdict (`runChecker_exampleTree`)
    yields a concrete sound consequence. -/
theorem exampleTree_runnable_sound :
    ∃ checked : CheckedFoundationProof (1 : Credence) Nat Nat,
      checkFoundationCertificate (1 : Credence) exampleTree = some checked ∧
      FoundationThresholdConsequence.{0, 0, w} (1 : Credence)
        checked.premises checked.conclusion :=
  runChecker_true_sound runChecker_exampleTree

end Structure
end Foundation
end Cred
