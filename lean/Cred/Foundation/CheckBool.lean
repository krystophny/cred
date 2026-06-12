/-
  Cred Foundation Credence-free Checker

  The verified checker `checkFoundationCertificate` carries a threshold
  `t : Credence`, whose carrier is `ℝ`, so its instance at a concrete signature
  is noncomputable and the Lean code generator cannot emit a standalone binary.

  Inspecting `applyFoundationRuleUnchecked` shows that `t` appears *only* in the
  result type `CheckedFoundationProof t`; every accept/reject decision (which
  payload branch returns `some`, the membership and equality side conditions)
  is independent of the value of `t`. This module exploits that: it defines a
  Credence-free checker `checkJudgment` that mirrors
  `applyFoundationRuleUnchecked`/`checkFoundationCertificate` case for case, but
  returns the `(premises, conclusion)` judgment instead of a typed proof. The
  result mentions no `Credence` and is computable, so it extracts to a real-free
  binary.

  The agreement theorem `checkJudgment_eq_map` proves, by mutual structural
  induction over the tree, that for every `t` the Credence-free run agrees with
  the verified run: `checkJudgment` equals the verified result mapped to its
  judgment, and hence the Boolean verdict `checkBool` equals the verified
  `isSome`. The soundness bridge `checkBool_true_sound` composes this with
  `checkFoundationCertificate_sound`, so the real-free verdict still entails the
  object-level consequence.
-/

import Cred.Extraction

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

/-- A Credence-free judgment: the premises and conclusion a checked step would
    carry, with no proof term and no threshold. -/
abbrev Judgment (Func : Type u) (Pred : Type v) :=
  List (Formula Func Pred) × Formula Func Pred

/-- Credence-free analogue of `applyFoundationRuleUnchecked`. It mirrors every
    payload case and side condition exactly, but consumes and produces bare
    `(premises, conclusion)` judgments instead of typed proofs. No `Credence`
    appears, so this is computable. -/
def applyRuleJudgment [DecidableEq Func] [DecidableEq Pred] :
    FoundationRulePayload Func Pred →
      List (Judgment Func Pred) →
      Option (Judgment Func Pred)
  | .hyp Γ φ, [] =>
      if φ ∈ Γ then some (Γ, φ) else none
  | .weaken Δ, [(Γ, φ)] =>
      if ∀ ψ ∈ Γ, ψ ∈ Δ then some (Δ, φ) else none
  | .cut mid, [(Γ, φ), (Δ, ψ)] =>
      if φ = mid then
        if Δ = mid :: Γ then some (Γ, ψ) else none
      else
        none
  | .conjElimLeft, [(Γ, conclusion)] =>
      match conclusion with
      | .conj φ _ => some (Γ, φ)
      | _ => none
  | .conjElimRight, [(Γ, conclusion)] =>
      match conclusion with
      | .conj _ ψ => some (Γ, ψ)
      | _ => none
  | .disjIntroLeft ψ, [(Γ, φ)] =>
      some (Γ, .disj φ ψ)
  | .disjIntroRight φ, [(Γ, ψ)] =>
      some (Γ, .disj φ ψ)
  | .equalityRefl Γ τ, [] =>
      some (Γ, .equal τ τ)
  | .equalitySymm, [(Γ, conclusion)] =>
      match conclusion with
      | .equal τ υ => some (Γ, .equal υ τ)
      | _ => none
  | .equalityTrans, [(Γ, conclusionP), (Δ, conclusionQ)] =>
      match conclusionP, conclusionQ with
      | .equal τ υ, .equal υ' χ =>
          if Γ = Δ then
            if υ = υ' then some (Γ, .equal τ χ) else none
          else
            none
      | _, _ => none
  | .equalitySubst τ υ φ, [(Γ, eqConclusion), (Δ, φConclusion)] =>
      if eqConclusion = .equal τ υ then
        if φConclusion = Formula.instantiate τ φ then
          if Γ = Δ then some (Γ, Formula.instantiate υ φ) else none
        else
          none
      else
        none
  | .forallElim τ, [(Γ, conclusion)] =>
      match conclusion with
      | .forallE φ => some (Γ, Formula.instantiate τ φ)
      | _ => none
  | .existsIntro φ τ, [(Γ, conclusion)] =>
      if conclusion = Formula.instantiate τ φ then
        some (Γ, .existsE φ)
      else
        none
  | _, _ => none

mutual

/-- Credence-free analogue of `checkFoundationCertificate`. -/
def checkJudgment [DecidableEq Func] [DecidableEq Pred] :
    FoundationCertificateTree Func Pred → Option (Judgment Func Pred)
  | .node payload children => do
      if children.length = payload.childCount then
        let checkedChildren ← checkJudgmentList children
        applyRuleJudgment payload checkedChildren
      else
        none

/-- Credence-free analogue of `checkFoundationCertificateList`. -/
def checkJudgmentList [DecidableEq Func] [DecidableEq Pred] :
    List (FoundationCertificateTree Func Pred) →
      Option (List (Judgment Func Pred))
  | [] => some []
  | child :: children => do
      let checkedChild ← checkJudgment child
      let checkedChildren ← checkJudgmentList children
      some (checkedChild :: checkedChildren)

end

/-- The Credence-free Boolean verdict. Computable, real-free, extractable. -/
def checkBool [DecidableEq Func] [DecidableEq Pred]
    (tree : FoundationCertificateTree Func Pred) : Bool :=
  (checkJudgment tree).isSome

/-- The judgment carried by a checked proof. -/
def CheckedFoundationProof.judgment {t : Credence}
    (checked : CheckedFoundationProof t Func Pred) : Judgment Func Pred :=
  (checked.premises, checked.conclusion)

/-- Single-step agreement: the Credence-free rule application agrees with the
    typed one, mapped down to its judgment. The argument lists are linked by the
    same `judgment` map. -/
theorem applyRuleJudgment_eq_map [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (payload : FoundationRulePayload Func Pred)
    (children : List (CheckedFoundationProof t Func Pred)) :
    applyRuleJudgment payload (children.map CheckedFoundationProof.judgment) =
      (applyFoundationRuleUnchecked t payload children).map
        CheckedFoundationProof.judgment := by
  cases payload <;>
    rcases children with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩ <;>
    (try rcases c0 with ⟨Γ, φ, p⟩) <;>
    (try rcases c1 with ⟨Δ, ψ, q⟩) <;>
    simp only [List.map, applyRuleJudgment, applyFoundationRuleUnchecked,
      CheckedFoundationProof.judgment]
  -- Payloads whose acceptance inspects a child conclusion need that conclusion
  -- destructed so both matches reduce together.
  case conjElimLeft.cons.nil => cases φ <;> rfl
  case conjElimRight.cons.nil => cases φ <;> rfl
  case equalitySymm.cons.nil => cases φ <;> rfl
  case forallElim.cons.nil => cases φ <;> rfl
  case equalityTrans.cons.cons.nil =>
    cases φ <;> cases ψ <;>
      simp only [applyRuleJudgment, applyFoundationRuleUnchecked,
        CheckedFoundationProof.judgment] <;>
      (repeat' split) <;> rfl
  all_goals (first | rfl | ((repeat' split) <;> rfl))

/-- The verified list checker preserves length. -/
theorem checkFoundationCertificateList_length [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} :
    ∀ {trees : List (FoundationCertificateTree Func Pred)}
      {checked : List (CheckedFoundationProof t Func Pred)},
      checkFoundationCertificateList t trees = some checked →
      checked.length = trees.length
  | [], checked, h => by
      simp only [checkFoundationCertificateList] at h
      cases h; rfl
  | tree :: trees, checked, h => by
      simp only [checkFoundationCertificateList] at h
      cases htree : checkFoundationCertificate t tree with
      | none => rw [htree] at h; simp at h
      | some checkedTree =>
          rw [htree] at h
          cases htrees : checkFoundationCertificateList t trees with
          | none => rw [htrees] at h; simp at h
          | some checkedTrees =>
              rw [htrees] at h
              simp only [Option.some_bind, Option.bind_eq_bind] at h
              cases h
              simp [checkFoundationCertificateList_length htrees]

mutual

/-- Core agreement, tree case: for every `t`, the Credence-free run equals the
    verified run mapped to its judgment. Proved by mutual structural induction. -/
theorem checkJudgment_eq_map [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (tree : FoundationCertificateTree Func Pred) :
    checkJudgment tree =
      (checkFoundationCertificate t tree).map
        CheckedFoundationProof.judgment := by
  cases tree with
  | node payload children =>
      by_cases hcount : children.length = payload.childCount
      · have hlist := checkJudgmentList_eq_map t children
        simp only [checkJudgment, checkFoundationCertificate, hcount,
          if_true]
        cases hcheck : checkFoundationCertificateList t children with
        | none =>
            rw [hcheck] at hlist
            simp [hlist]
        | some checkedChildren =>
            rw [hcheck] at hlist
            have hlen : checkedChildren.length = payload.childCount := by
              rw [checkFoundationCertificateList_length hcheck]; exact hcount
            simp only [hlist, Option.map_some', Option.some_bind,
              Option.bind_eq_bind]
            rw [applyRuleJudgment_eq_map t payload checkedChildren,
              applyFoundationRule, hlen, if_pos rfl]
      · simp only [checkJudgment, checkFoundationCertificate, hcount,
          if_false]
        rfl

/-- Core agreement, list case. -/
theorem checkJudgmentList_eq_map [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (trees : List (FoundationCertificateTree Func Pred)) :
    checkJudgmentList trees =
      (checkFoundationCertificateList t trees).map
        (fun cs => cs.map CheckedFoundationProof.judgment) := by
  cases trees with
  | nil =>
      simp [checkJudgmentList, checkFoundationCertificateList]
  | cons tree trees =>
      have htree := checkJudgment_eq_map t tree
      have htrees := checkJudgmentList_eq_map t trees
      simp only [checkJudgmentList, checkFoundationCertificateList]
      cases hcheck : checkFoundationCertificate t tree with
      | none =>
          rw [hcheck] at htree
          simp [htree]
      | some checkedTree =>
          rw [hcheck] at htree
          simp only [htree, Option.map_some', Option.some_bind,
            Option.bind_eq_bind]
          cases hchecks : checkFoundationCertificateList t trees with
          | none =>
              rw [hchecks] at htrees
              simp [htrees]
          | some checkedTrees =>
              rw [hchecks] at htrees
              simp [htrees]

end

/-- Boolean-verdict agreement: the Credence-free verdict equals the verified
    `isSome` for every threshold. This is exactly what extraction needs. -/
theorem checkBool_eq_isSome [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (tree : FoundationCertificateTree Func Pred) :
    checkBool tree = (checkFoundationCertificate t tree).isSome := by
  unfold checkBool
  rw [checkJudgment_eq_map t tree, Option.isSome_map']

/-- When the Credence-free verdict accepts, the verified checker also produces a
    certificate, and the Credence-free judgment is that certificate's judgment. -/
theorem checkBool_true_checked [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (tree : FoundationCertificateTree Func Pred)
    (h : checkBool tree = true) :
    ∃ checked : CheckedFoundationProof t Func Pred,
      checkFoundationCertificate t tree = some checked ∧
      checkJudgment tree = some checked.judgment := by
  rw [checkBool_eq_isSome t tree] at h
  cases hcheck : checkFoundationCertificate t tree with
  | none => rw [hcheck] at h; simp at h
  | some checked =>
      refine ⟨checked, rfl, ?_⟩
      rw [checkJudgment_eq_map t tree, hcheck, Option.map_some']

/-- Soundness bridge: a `true` real-free verdict entails the object-level
    consequence at threshold `t`. The verdict is computed without any reals; the
    soundness it witnesses lives in the verified `Credence` layer. -/
theorem checkBool_true_sound [DecidableEq Func] [DecidableEq Pred]
    (t : Credence) (tree : FoundationCertificateTree Func Pred)
    (h : checkBool tree = true) :
    ∃ checked : CheckedFoundationProof t Func Pred,
      checkFoundationCertificate t tree = some checked ∧
      FoundationThresholdConsequence.{u, v, w} t
        checked.premises checked.conclusion := by
  obtain ⟨checked, hcheck, _⟩ := checkBool_true_checked t tree h
  exact ⟨checked, hcheck, checkFoundationCertificate_sound hcheck⟩

/-- The Credence-free verdict accepts the concrete example tree, by computation
    alone (no reals involved). -/
theorem checkBool_exampleTree : checkBool exampleTree = true := by
  rfl

/-- Specialised soundness bridge for the example tree at threshold `1`. -/
theorem checkBool_exampleTree_sound :
    ∃ checked : CheckedFoundationProof (1 : Credence) Nat Nat,
      checkFoundationCertificate (1 : Credence) exampleTree = some checked ∧
      FoundationThresholdConsequence.{0, 0, w} (1 : Credence)
        checked.premises checked.conclusion :=
  checkBool_true_sound (1 : Credence) exampleTree checkBool_exampleTree

-- Real-free executable verdict on the concrete tree: prints `true`.
#eval checkBool exampleTree

/-- Standalone entry point: run the Credence-free checker on the example tree and
    report the verdict. `lake` can compile this to a binary with no reals in the
    trusted base. -/
def main : IO Unit :=
  IO.println s!"checkBool exampleTree = {checkBool exampleTree}"

end Structure
end Foundation
end Cred
