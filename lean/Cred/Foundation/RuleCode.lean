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

def trustedFoundationRules : List FoundationRuleCode :=
  [.hyp, .weaken, .cut, .conjElimLeft, .conjElimRight, .disjIntroLeft,
    .disjIntroRight, .equalityRefl, .equalitySymm, .equalityTrans,
    .equalitySubst, .forallElim, .existsIntro]

theorem mem_trustedFoundationRules (r : FoundationRuleCode) :
    r ∈ trustedFoundationRules := by
  cases r <;> simp [trustedFoundationRules]

end Structure

end Foundation
end Cred
