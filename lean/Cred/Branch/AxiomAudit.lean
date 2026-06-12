/-
  Cred Branch: Classical-Axiom Dependence Audit (issue #523)

  Each `#print axioms` command causes the elaborator to surface which of the
  four Lean 4 kernel axioms a theorem ultimately depends on:
    propext        — propositional extensionality
    funext         — function extensionality (encoded via propext in Lean 4)
    Classical.choice — excluded middle / choice
    Quot.sound     — quotient soundness

  Groups mirror the repo layers. The measured profile is uniform: every
  audited theorem depends on exactly [propext, Classical.choice, Quot.sound].
  The Credence value type is a subtype of the Mathlib reals, so even the
  pure interval-arithmetic results inherit all three axioms transitively
  through Mathlib's real-number development (order/field instances built on
  Cauchy-sequence quotients use Quot.sound, and the classical order/decidability
  instances pull in Classical.choice). No audited theorem adds an axiom beyond
  these three, and none reduces below them.
-/

import Cred.Core.Value
import Cred.Cond.Admissible
import Cred.Bridge.CondBridge
import Cred.Bridge.Crisp
import Cred.Bridge.Curry
import Cred.Set.Russell
import Cred.Set.Quine
import Cred.Foundation.CheckerSoundness

-- Core/Value: interval arithmetic over the Mathlib reals. The real-number
-- order and field instances carry all three kernel axioms transitively.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Credence.neg_fixed_point_unique
#print axioms Cred.Credence.conditioning_zero_any
#print axioms Cred.Credence.conditioning_unique

-- Bridge/CondBridge: noncomputable reals (min/div) plus `by_cases` case splits.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.no_truthfunctional_cond_bridge

-- Bridge/Crisp: `crisp_exists_bool` branches on an if-then-else under `classical`.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.crisp_embedding

-- Bridge/Curry: prodResid is noncomputable (Real.sqrt, min/div); curry_block
-- uses `by_cases` internally via prodResid_unique_positive.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Credence.curry_block

-- Set/Russell and Set/Quine: ofPred uses `open Classical` and `decide` on an
-- arbitrary Prop, which requires Classical.choice (propDecidable).
-- signedQuine_self_eq_half delegates to russell_fixed_point → neg_fixed_point_unique.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.CredSet.russell_mem_eq_half
#print axioms Cred.CredSet.signedQuine_self_eq_half

-- Foundation/CheckerSoundness: the proof chain runs through FoundationProof.sound;
-- Mathlib's Real imports carry all three kernel axioms transitively.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Foundation.Structure.checkFoundationCertificate_sound
