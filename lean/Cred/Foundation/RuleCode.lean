/-
  Cred Foundation Rule Codes

  Rule codes name the trusted constructors a future external checker must
  validate before producing `FoundationProof` certificates.
-/

import Cred.Foundation.Kernel

namespace Cred
namespace Foundation

namespace Structure

inductive FoundationRuleCode where
  | hyp
  | weaken
  | cut
  | conjElimLeft
  | conjElimRight
  | disjIntroLeft
  | disjIntroRight
  | equalityRefl
  | equalitySymm
  | equalityTrans
  | equalitySubst
  | forallElim
  | existsIntro
deriving Repr, DecidableEq

def FoundationRuleCode.name : FoundationRuleCode → String
  | .hyp => "hyp"
  | .weaken => "weaken"
  | .cut => "cut"
  | .conjElimLeft => "conjElimLeft"
  | .conjElimRight => "conjElimRight"
  | .disjIntroLeft => "disjIntroLeft"
  | .disjIntroRight => "disjIntroRight"
  | .equalityRefl => "equalityRefl"
  | .equalitySymm => "equalitySymm"
  | .equalityTrans => "equalityTrans"
  | .equalitySubst => "equalitySubst"
  | .forallElim => "forallElim"
  | .existsIntro => "existsIntro"

def FoundationRuleCode.ofName : String → Option FoundationRuleCode
  | "hyp" => some .hyp
  | "weaken" => some .weaken
  | "cut" => some .cut
  | "conjElimLeft" => some .conjElimLeft
  | "conjElimRight" => some .conjElimRight
  | "disjIntroLeft" => some .disjIntroLeft
  | "disjIntroRight" => some .disjIntroRight
  | "equalityRefl" => some .equalityRefl
  | "equalitySymm" => some .equalitySymm
  | "equalityTrans" => some .equalityTrans
  | "equalitySubst" => some .equalitySubst
  | "forallElim" => some .forallElim
  | "existsIntro" => some .existsIntro
  | _ => none

theorem FoundationRuleCode.ofName_name (r : FoundationRuleCode) :
    FoundationRuleCode.ofName r.name = some r := by
  cases r <;> rfl

def trustedFoundationRules : List FoundationRuleCode :=
  [.hyp, .weaken, .cut, .conjElimLeft, .conjElimRight, .disjIntroLeft,
    .disjIntroRight, .equalityRefl, .equalitySymm, .equalityTrans,
    .equalitySubst, .forallElim, .existsIntro]

theorem mem_trustedFoundationRules (r : FoundationRuleCode) :
    r ∈ trustedFoundationRules := by
  cases r <;> simp [trustedFoundationRules]

theorem FoundationRuleCode.ofName_eq_some_mem
    {s : String} {r : FoundationRuleCode}
    (_h : FoundationRuleCode.ofName s = some r) :
    r ∈ trustedFoundationRules :=
  mem_trustedFoundationRules r

end Structure

end Foundation
end Cred
