/-
  Cred: Cromwell's Rule and the No-Ex-Falso Tie

  Two faces of zero credence, formalized over the existing Bayesian update.

  Cromwell face: a zero evidence/joint credence is an absorbing fixed point of
  the multiplicative chain-rule update. Whatever conditional credence is chosen,
  the posterior joint stays 0, so a zero prior can never be revised to a
  positive value by multiplicative updating.

  No-ex-falso face: the same zero evidence leaves the conditional itself
  completely unconstrained (conditioning_zero_any). The dead joint and the free
  conditional are the same phenomenon: c ⊗ 0 = 0 says nothing about c.

  Historical attribution (Cromwell, Lindley) lives in the prose, not here.
-/

import Cred.Update

namespace Cred

namespace Credence

/-! ## Cromwell: zero is an absorbing fixed point of the multiplicative update -/

/-- Zero evidence absorbs every conditional: the multiplicative update sends any
    candidate posterior conditional to joint credence 0. -/
theorem cromwell_zero_absorbing (c : Credence) : c ⊗ (0 : Credence) = 0 :=
  conj_zero c

/-- No conditional revises zero evidence to a positive joint: the chain-rule
    update cannot produce a positive result from zero evidence. -/
theorem cromwell_no_positive_revision (c : Credence) :
    ¬ 0 < (c ⊗ (0 : Credence)).val := by
  rw [cromwell_zero_absorbing]
  exact lt_irrefl 0

/-- The Cromwell fixed point: any conditioning structure on zero evidence has
    joint credence 0. A zero prior stays zero under the chain rule. -/
theorem cromwell_fixed_point (joint : Credence) (cond : Conditioning joint 0) :
    joint = 0 :=
  conditioning_zero_forces_joint_zero joint cond

/-! ## The tie: dead joint, free conditional

The chain rule `c ⊗ 0 = 0` forces the joint to 0 (Cromwell) precisely because
the product erases c (no ex falso). The single fact below names both faces. -/

/-- Cromwell / no-ex-falso correspondence: at zero evidence every conditional
    yields joint 0 (absorbing, no positive revision), and every conditional is
    admissible (unconstrained, no ex falso). One equation, two readings. -/
theorem cromwell_no_ex_falso_tie (c : Credence) :
    c ⊗ (0 : Credence) = 0 ∧ ∃ cond : Conditioning 0 0, cond.condCred = c :=
  ⟨conj_zero c, conditioning_zero_any c⟩

end Credence

/-! ## Cromwell over the Bayesian update

`bayesianUpdate` is defined only for positive evidence (`0 < evidence.val`): the
update mechanism refuses zero evidence outright. The Cromwell statements below
phrase the tie at this boundary. -/

/-- The Bayesian update is never applied at zero evidence: its positivity
    precondition excludes the absorbing point. This is Cromwell's rule as a
    side condition on the update. -/
theorem bayesianUpdate_requires_positive_evidence (joint evidence : Credence)
    (h_pos : 0 < evidence.val) (_h_le : joint.val ≤ evidence.val) :
    evidence ≠ 0 := by
  intro h
  rw [h] at h_pos
  exact lt_irrefl 0 h_pos

/-- The Cromwell tie at the Bayesian-update boundary: where the update is
    forbidden (zero evidence), the chain rule both pins the joint to 0 and
    leaves the posterior conditional free. The Bayesian update covers exactly
    the positive-evidence complement (bayesianUpdate_chain_rule). -/
theorem bayesian_cromwell_tie (c : Credence) :
    c ⊗ (0 : Credence) = 0 ∧
      ∀ posterior : Credence, ∃ cond : Credence.Conditioning 0 0,
        cond.condCred = posterior :=
  ⟨Credence.conj_zero c, Credence.conditioning_zero_any⟩

end Cred
