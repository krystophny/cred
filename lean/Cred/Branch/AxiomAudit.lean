/-
  Cred Branch: Classical-Axiom Dependence Audit (issue #523)

  Each `#print axioms` command causes the elaborator to surface which of the
  four Lean 4 kernel axioms a theorem ultimately depends on:
    propext        — propositional extensionality
    funext         — function extensionality (encoded via propext in Lean 4)
    Classical.choice — excluded middle / choice
    Quot.sound     — quotient soundness

  Groups mirror the repo layers. Every theorem that touches the Credence value
  type depends on exactly [propext, Classical.choice, Quot.sound]. The Credence
  value type is a subtype of the Mathlib reals, so even the pure
  interval-arithmetic results inherit all three axioms transitively through
  Mathlib's real-number development (order/field instances built on
  Cauchy-sequence quotients use Quot.sound, and the classical order/decidability
  instances pull in Classical.choice). No such theorem adds an axiom beyond
  these three.

  The generic aggregation layer is the exception, and it is the expected one:
  `consequence_cut` is carrier-agnostic and reduces to [propext] alone, and
  `boolean_forall_consequence_is_classical` is a definitional unfolding over
  `Bool` that depends on no axioms at all. Neither uses the Credence carrier or
  Mathlib reals, so neither inherits Classical.choice or Quot.sound. No audited
  theorem depends on sorryAx.
-/

import Cred.Core.Value
import Cred.Cond.Admissible
import Cred.Bridge.CondBridge
import Cred.Bridge.Crisp
import Cred.Bridge.Curry
import Cred.Set.Russell
import Cred.Set.Quine
import Cred.Foundation.CheckerSoundness
import Cred.Aggregation.Specializations
import Cred.Native.Basic
import Cred.Cond.Uniqueness
import Cred.Probability.Cox
import Cred.Probability.FuzzyObservable
import Cred.Foundation.ClassicalRecovery
import Cred.Foundation.Induction
import Cred.Foundation.HigherLayerDemo
import Cred.Approx.ScoreRecipes
import Cred.Set.FuzzyExamples
import Cred.Approx.NumericsExamples
import Cred.Examples.Fractal
import Cred.Math.Continuity
import Cred.Math.Smoothness
import Cred.Math.Dimension
import Cred.Topology.Manifold
import Cred.Topology.ManifoldN
import Cred.Probability.CoxUniqueness

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

-- Aggregation/ForallConsequence + Specializations: the generic forall-consequence
-- structural rules and the Boolean classical anchor. consequence_cut is the
-- generic cut; boolean_forall_consequence_is_classical is a definitional
-- unfolding to classical consequence. Measured: propext, Classical.choice,
-- Quot.sound (inherited through the Credence carrier and Mathlib).
#print axioms Cred.Aggregation.consequence_cut
#print axioms Cred.Aggregation.boolean_forall_consequence_is_classical

-- Native/Basic: residuum-versus-fiber divergence at the impossible point, the
-- non-explosion mechanism of native Cred. Measured: propext, Classical.choice,
-- Quot.sound.
#print axioms Cred.Native.residuum_vs_fiber_zero

-- Cond/Uniqueness: any chain-rule-faithful set-valued conditional semantics
-- equals Cond pointwise. Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Credence.chainRuleFaithful_eq_Cond

-- Probability/Cox: the conservative finite Cox representation (additivity to
-- measure). Probability/FuzzyObservable: probability as the expectation of a
-- 0/1 observable. Both are finite rational sums but inherit the three axioms
-- through Mathlib's rational/Finset development. Measured: propext,
-- Classical.choice, Quot.sound.
#print axioms Cred.Probability.cox_finite_representation
#print axioms Cred.Probability.expectation_indicator

-- Foundation/ClassicalRecovery: classical propositional logic is exactly the
-- crisp fragment. The crisp bridge branches under `classical` and rides the
-- Credence carrier. Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Foundation.classical_propositional_is_fragment

-- Foundation/Induction: induction soundness in the standard arithmetic model,
-- by `Nat.rec` lifted to object formulas through Mathlib reals.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Foundation.arithQ.foundation_induction_sound

-- Foundation/HigherLayerDemo: a higher layer derives a classical consequence by
-- composing foundation kernel rules (equalitySymm + equalitySubst) through
-- FoundationProof.sound. Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Foundation.Demo.higher_layer_builds_on_foundation

-- Approx/ScoreRecipes: the rational residual-to-score recipe is antitone in the
-- residual. Pure exact rational arithmetic (max, division, linarith/gcongr), but
-- the rational order/field instances ride Mathlib. Measured: propext,
-- Classical.choice, Quot.sound.
#print axioms Cred.Approx.Rat.scoreEps_mono

-- Set/FuzzyExamples: the crisp membership function recovers its classical set on
-- the nose and takes only the values {0,1}. Rides the Credence carrier through
-- credence_zero_ne_one. Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.CredSet.fuzzy_membership_crisp_recovery

-- Examples/Fractal: the finite box-count estimate log(2^k)/log(3^k) equals the
-- Cantor similarity dimension log 2/log 3 for every k ≥ 1. Uses Mathlib Real.log;
-- the k's cancel by log_pow. Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Examples.Fractal.box_estimate_eq_dim

-- Approx/NumericsExamples: numerics status anchor. The full explicit-Euler step
-- h = 1 hits the conservation scale, so the structure degree collapses to the
-- impossibility credence. Rides the real-valued scoreEpsCredence and the
-- Credence carrier. Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Approx.explicitEuler_full_step_degree_zero

-- Math/Continuity: classical ε-δ continuity is the meet over all threshold
-- continuities. The recovery rides the Credence carrier and Mathlib's metric
-- topology. Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Math.tcontinuousAt_all_iff_continuousAt

-- Math/Smoothness: the load-bearing kink witness, status 0 at the |·| corner,
-- via Mathlib's not_differentiableAt_abs_zero. Measured: propext,
-- Classical.choice, Quot.sound.
#print axioms Cred.Math.diffStatus_abs_zero

-- Math/Dimension: the Moran / open-set-condition equation for an n-map
-- equal-ratio IFS, generalizing the Cantor instance. Uses Mathlib Real.rpow/log.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Math.moran_general

-- Topology/Manifold: the identity transition carries smooth status, the seed
-- closure fact through ContDiff. Rides the Credence carrier and Mathlib ContDiff.
-- Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Manifold.transitionSmoothness_id

-- Topology/ManifoldN: the n-dimensional headline recovery — atlas smoothness
-- status equals certainty iff M is a genuine Mathlib IsManifold for the Euclidean
-- model at the analytic order. Rides the Credence carrier and Mathlib's
-- contDiffGroupoid / IsManifold development. Measured: propext, Classical.choice,
-- Quot.sound.
#print axioms Cred.ManifoldN.atlasSmoothStatus_eq_one_iff_isManifold

-- Probability/CoxUniqueness: any two finite measures representing the same
-- plausibility agree on every event. Finite rational sums, inheriting the three
-- axioms through Mathlib. Measured: propext, Classical.choice, Quot.sound.
#print axioms Cred.Probability.cox_representation_unique
