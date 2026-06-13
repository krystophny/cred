/-
  Native Continuum Cred: Rigidity and Recovery Anchors

  Paper-facing wrappers that name, for the native continuum-valued Cred, the
  rigidity and recovery results already established elsewhere. Nothing is
  re-proved here; each theorem cites an existing result.

  - nativeCred_crisp_closed: a valuation taking only crisp atom values {0,1}
    evaluates every formula in {0,1}, and that value is the classical Boolean
    evaluation read through the embedding (reuse Cred.evalCred_crisp and
    Cred.crisp_eval_eq from Bridge/Crisp.lean).
  - nativeCred_unique_three_quotient: the Kleene lattice is the unique
    three-element quotient (alias of three_element_quotient_unique).
  - nativeCred_no_finite_real_quotient: no non-trivial finite quotient exists
    under full real multiplication (alias of
    RealCongruence.no_nontrivial_finite_quotient).
-/

import Cred.Bridge.Crisp
import Cred.Congruence.Real

namespace Cred.Native

variable {α : Type*}

/-! ## Crisp closure and Boolean recovery -/

/-- Native crisp closure: if every atom value is crisp ({0,1}), then every
    formula evaluates to a crisp value, and that value coincides with the
    classical Boolean evaluation through the embedding. Reuses
    `Cred.evalCred_crisp` and `Cred.crisp_eval_eq`. -/
theorem nativeCred_crisp_closed (v : α → Bool) (φ : Formula α) :
    (Cred.evalCred (fun a => Cred.embed (v a)) φ = 0 ∨
       Cred.evalCred (fun a => Cred.embed (v a)) φ = 1) ∧
    Cred.evalCred (fun a => Cred.embed (v a)) φ = Cred.embed (Cred.classicalEval v φ) :=
  ⟨Cred.evalCred_crisp (fun a => Cred.embed (v a)) (fun a => Cred.embed_crisp (v a)) φ,
    Cred.crisp_eval_eq v φ⟩

/-! ## Quotient rigidity -/

/-- Native uniqueness of the three-element quotient: any surjective
    neg/conj-homomorphism from the credence algebra to the three-valued
    quotient is the Kleene lattice (up to the 0/1 swap). Alias of
    `three_element_quotient_unique`. -/
theorem nativeCred_unique_three_quotient
    (φ : Cred.Credence → Cred.ThreeVal)
    (hsurj : Function.Surjective φ)
    (hneg : ∀ c, φ (Cred.Credence.neg c) = Cred.ThreeVal.neg (φ c))
    (hconj : ∀ c₁ c₂, φ (c₁ ⊗ c₂) = Cred.ThreeVal.conj (φ c₁) (φ c₂)) :
    φ 0 = Cred.ThreeVal.zero ∧ φ 1 = Cred.ThreeVal.one ∧
        φ Cred.Credence.half = Cred.ThreeVal.half
    ∨ φ 0 = Cred.ThreeVal.one ∧ φ 1 = Cred.ThreeVal.zero ∧
        φ Cred.Credence.half = Cred.ThreeVal.half :=
  Cred.three_element_quotient_unique φ hsurj hneg hconj

/-- Native real-multiplication rigidity: no non-trivial finite quotient exists
    under full real multiplication. Alias of
    `RealCongruence.no_nontrivial_finite_quotient`. -/
theorem nativeCred_no_finite_real_quotient
    (R : Cred.RealCongruence) (hnt : R.NonTrivial)
    (nclasses : ℕ)
    (classify : ℝ → Fin nclasses)
    (hquot : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      classify a = classify b → R.rel a b) :
    False :=
  Cred.RealCongruence.no_nontrivial_finite_quotient R hnt nclasses classify hquot

end Cred.Native
