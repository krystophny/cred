/-
  Cred Coherence: sequential equals batch updating.

  When the joint model is fixed, conditioning in one step on the combined
  evidence equals conditioning sequentially through an intermediate event. For
  nested credence values small <= mid <= big, the Bayesian update is division,
  and the intermediate cancels: small/big = (small/mid) * (mid/big). This is the
  multiplicative coherence of the chain rule.
-/

import Cred.Update

namespace Cred

/-- Sequential equals batch updating for nested evidence with a fixed joint.
    Conditioning `small` on `big` directly (batch) equals conditioning on the
    intermediate `mid` and then composing `mid` on `big` (sequential). The
    intermediate event cancels. -/
theorem sequential_eq_batch (small mid big : Credence)
    (hmid : 0 < mid.val) (hbig : 0 < big.val)
    (h_sm : small.val ≤ mid.val) (h_mb : mid.val ≤ big.val) :
    bayesianUpdate small big hbig (le_trans h_sm h_mb)
      = bayesianUpdate small mid hmid h_sm ⊗ bayesianUpdate mid big hbig h_mb := by
  have hm : mid.val ≠ 0 := ne_of_gt hmid
  have hb : big.val ≠ 0 := ne_of_gt hbig
  ext
  simp only [Credence.conj_val, bayesianUpdate_val]
  field_simp

/-- The composed sequential update satisfies the same chain rule as the batch
    update: it is a coherent posterior. -/
theorem sequential_chain_rule (small mid big : Credence)
    (hmid : 0 < mid.val) (hbig : 0 < big.val)
    (h_sm : small.val ≤ mid.val) (h_mb : mid.val ≤ big.val) :
    (bayesianUpdate small mid hmid h_sm ⊗ bayesianUpdate mid big hbig h_mb) ⊗ big
      = small := by
  rw [← sequential_eq_batch small mid big hmid hbig h_sm h_mb]
  exact bayesianUpdate_chain_rule small big hbig (le_trans h_sm h_mb)

end Cred
