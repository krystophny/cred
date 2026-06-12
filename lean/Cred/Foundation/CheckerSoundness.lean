/-
  Cred Foundation Checker Soundness

  Verifier theorems for checked foundation certificate trees.
-/

import Cred.Foundation.Checker

namespace Cred
namespace Foundation

universe u v w

namespace Structure

variable {Func : Type u} {Pred : Type v}

theorem CheckedFoundationProof.sound
    {t : Credence} (checked : CheckedFoundationProof t Func Pred) :
    FoundationThresholdConsequence.{u, v, w} t
      checked.premises checked.conclusion :=
  FoundationProof.sound checked.proof

theorem checkFoundationCertificate_some_arityMatches
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificate t tree = some checked) :
    tree.arityMatches := by
  cases tree with
  | node payload children =>
      by_cases hcount : children.length = payload.childCount
      · exact hcount
      · simp [checkFoundationCertificate, FoundationCertificateTree.arityMatches,
          FoundationCertificateTree.children,
          FoundationCertificateTree.childCount,
          FoundationCertificateTree.ruleCode, hcount] at h

mutual

theorem checkFoundationCertificate_some_allAritiesMatch
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificate t tree = some checked) :
    tree.allAritiesMatch := by
  cases tree with
  | node payload children =>
      by_cases hcount : children.length = payload.childCount
      · simp [checkFoundationCertificate, hcount] at h
        cases hchildren : checkFoundationCertificateList t children with
        | none =>
            simp [hchildren] at h
        | some checkedChildren =>
            simp [hchildren] at h
            simp [FoundationCertificateTree.allAritiesMatch,
              FoundationCertificateTree.arityMatches,
              FoundationCertificateTree.children,
              FoundationCertificateTree.childCount,
              FoundationCertificateTree.ruleCode]
            exact
              ⟨hcount,
                checkFoundationCertificateList_some_allAritiesMatchList hchildren⟩
      · simp [checkFoundationCertificate, hcount] at h

theorem checkFoundationCertificateList_some_allAritiesMatchList
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {trees : List (FoundationCertificateTree Func Pred)}
    {checked : List (CheckedFoundationProof t Func Pred)}
    (h : checkFoundationCertificateList t trees = some checked) :
    FoundationCertificateTree.allAritiesMatchList trees := by
  cases trees with
  | nil =>
      simp [FoundationCertificateTree.allAritiesMatchList]
  | cons tree trees =>
      simp [checkFoundationCertificateList] at h
      cases htree : checkFoundationCertificate t tree with
      | none =>
          simp [htree] at h
      | some checkedTree =>
          cases htrees : checkFoundationCertificateList t trees with
          | none =>
              simp [htree, htrees] at h
          | some checkedTrees =>
              simp [htree, htrees] at h
              exact
                ⟨checkFoundationCertificate_some_allAritiesMatch htree,
                  checkFoundationCertificateList_some_allAritiesMatchList htrees⟩

end

mutual

theorem checkFoundationCertificate_some_shapeOK
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (h : checkFoundationCertificate t tree = some checked) :
    tree.shapeOK = true := by
  cases tree with
  | node payload children =>
      by_cases hcount : children.length = payload.childCount
      · simp [checkFoundationCertificate, hcount] at h
        cases hchildren : checkFoundationCertificateList t children with
        | none =>
            simp [hchildren] at h
        | some checkedChildren =>
            have hshapeList :=
              checkFoundationCertificateList_some_shapeOKList hchildren
            simp [FoundationCertificateTree.shapeOK, hcount, hchildren,
              hshapeList]
      · simp [checkFoundationCertificate, hcount] at h

theorem checkFoundationCertificateList_some_shapeOKList
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {trees : List (FoundationCertificateTree Func Pred)}
    {checked : List (CheckedFoundationProof t Func Pred)}
    (h : checkFoundationCertificateList t trees = some checked) :
    FoundationCertificateTree.shapeOKList trees = true := by
  cases trees with
  | nil =>
      simp [FoundationCertificateTree.shapeOKList]
  | cons tree trees =>
      simp [checkFoundationCertificateList] at h
      cases htree : checkFoundationCertificate t tree with
      | none =>
          simp [htree] at h
      | some checkedTree =>
          cases htrees : checkFoundationCertificateList t trees with
          | none =>
              simp [htree, htrees] at h
          | some checkedTrees =>
              have hshape :=
                checkFoundationCertificate_some_shapeOK htree
              have hshapes :=
                checkFoundationCertificateList_some_shapeOKList htrees
              simp [FoundationCertificateTree.shapeOKList, hshape, hshapes]

end

theorem checkFoundationCertificate_none_of_shapeOK_false
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    (hshape : tree.shapeOK = false) :
    checkFoundationCertificate t tree = none := by
  cases hcheck : checkFoundationCertificate t tree with
  | none => rfl
  | some checked =>
      have hok := checkFoundationCertificate_some_shapeOK hcheck
      rw [hshape] at hok
      contradiction

theorem checkFoundationCertificateList_none_of_shapeOKList_false
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {trees : List (FoundationCertificateTree Func Pred)}
    (hshape : FoundationCertificateTree.shapeOKList trees = false) :
    checkFoundationCertificateList t trees = none := by
  cases hcheck : checkFoundationCertificateList t trees with
  | none => rfl
  | some checked =>
      have hok := checkFoundationCertificateList_some_shapeOKList hcheck
      rw [hshape] at hok
      contradiction

theorem checkFoundationCertificate_sound
    [DecidableEq Func] [DecidableEq Pred]
    {t : Credence} {tree : FoundationCertificateTree Func Pred}
    {checked : CheckedFoundationProof t Func Pred}
    (_h : checkFoundationCertificate t tree = some checked) :
    FoundationThresholdConsequence.{u, v, w} t
      checked.premises checked.conclusion :=
  checked.sound

end Structure

end Foundation
end Cred
