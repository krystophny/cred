# Foundation track roadmap

Cred is a foundation *track* for topology, manifolds, and differential
geometry. It does not replace Mathlib's foundations of those subjects.

## Disclaimer (read first)

Mathlib owns the classical definitions: open sets, topological spaces,
continuous maps, charts, atlases, smooth manifolds, connections,
integrators. Cred does not redefine them and does not compete with them.
Where Cred needs a classical fact it imports the Mathlib statement.

What Cred adds sits *on top of* the classical structure: a graded status,
a provenance trail, and a structure-preservation score. The classical
predicate answers yes or no. Cred answers with a credence in [0,1], records
which evidence the credence rests on, and scores how well a numerical or
approximate object preserves a structure the classical theory only knows
as present or absent. The classical fact is the anchor; the graded layer is
the contribution.

This is a track of theorem-backed benchmarks, ordered by what already has a
Lean anchor and what is still future work. Each stage states what the
classical theory asks, what Cred adds, and the Lean anchor (or `future`).

## Stage 1: graded sets and graded topology

Lean anchor: `Cred/Set/Basic.lean`, `Cred/Topology/Basic.lean`,
`Cred/Topology/Graded.lean`, `Cred/Topology/Fuzzy.lean`,
`Cred/Topology/Threshold.lean`, `Cred/Topology/Clopen.lean`.

Classical asks: is a point in the set, is a set open, is a set clopen.
A `Set U` membership is a proposition; openness is a proposition closed
under the topology axioms.

Cred adds a membership credence and a graded openness. `CredSet U` carries
`mem : U -> Credence`; `inter` and `union` run through the product `⊗` and
its De Morgan dual `⊔`. `opennessDegree` and `closednessDegree` (in
`Topology/Graded.lean`) read off a credence rather than a bit. On crisp sets
the grade collapses back to 0 or 1, which the anchors prove:
`crisp_openness_zero_or_one`, `crisp_openness_one_iff_univ`,
`open_crisp_iff_isOpen` ties a crisp open `CredSet` to Mathlib's `IsOpen`.
The threshold cut `tcut` recovers a classical open set at each level
(`tcut_crisp`, `toPred_tcut`), so a single graded set yields a nested family
of classical opens. `Topology/Clopen.lean` keeps the classical side honest:
in the reals only `∅` and `univ` are clopen (`real_isClopen_iff_trivial`),
and a singleton is clopen only in the discrete topology.

Benchmark: graded openness monotone in the set (`openness_monotone`),
agreeing with Mathlib on crisp inputs, refining it on fuzzy inputs.

## Stage 2: structure-preserving numerics

Lean anchor: `Cred/Approx/Structure.lean`, `Cred/Approx/Score.lean`,
`Cred/Approx/Invariant.lean`, `Cred/Approx/Symplectic.lean`,
`Cred/Approx/Variational.lean`, `Cred/Approx/LieGroup.lean`.

Classical asks: does a map preserve a structure exactly. Symplecticity is
`Aᵀ J A = J`; an invariant is preserved when `I (Φ x) = I x`; a discrete
trajectory either lies on a Lie group or it does not.

Cred adds a preservation score and a degree. `StructureDegree` reads a
structure as a credence `P : X -> Credence`; `Preserves P Φ` means
`P (Φ x) = P x` pointwise; `PreservesAt t` and `AdmissibleApprox t` set a
threshold below which an approximation still counts. `scoreEps` (in
`Score.lean`) turns a residual `r` into a credence: 1 at zero residual,
decaying to 0 once the residual reaches the tolerance `eps`
(`scoreEps_one_of_zero`, `scoreEps_zero_of_ge`, `scoreEps_antitone`). Exact
preservation is the credence-1 boundary: `exactPreserves_iff_preservesAt_one`.
The concrete anchors check that the score tracks real geometry. The
symplectic group passes (`symplectic_one`, `symplectic_rotation`,
`symplectic_shear`) and a non-unit scaling fails (`not_symplectic_scaling`);
the leapfrog map satisfies the discrete Euler-Lagrange equation and conserves
the discrete momentum (`leapfrog_is_DEL`, `leapfrog_momentum_conserved`); a
group step stays on the Lie group while a coordinate shift leaves it
(`groupStep_preserves`, `coordStep_breaks_group`).

Benchmark: a numerical scheme gets a preservation credence per invariant,
exact when the residual is zero, graded under a stated tolerance, with the
preservation theorems as the anchor for the score's calibration.

## Stage 3: fractal and self-similarity status

Lean anchor: `Cred/Examples/RobustCollapse.lean`,
`Cred/Examples/RobustConditioning.lean`, `Cred/Examples/Sqrt2Branch.lean`,
`Cred/Examples/Branches.lean`, `Cred/Dependence/RobustCollapse.lean`.

Classical asks: is a value forced, is a contradiction present, does a
self-similar construction terminate. Each is a yes-or-no question.

Cred adds robustness status and a provenance chain. `RobustCollapse.lean`
separates the interior, where the collapsed value is robust to small
perturbation (`collapse_interval_interior_robust_half`), from the boundary,
where it is sensitive (`collapse_interval_boundary_sensitive`), and records
the zero-evidence case as underdetermined rather than contradictory
(`zero_evidence_collapse_underdetermined`). `RobustConditioning.lean` puts
numbers on it: a Fréchet interval `[3/10, 3/5]` for the joint, a product
joint of `21/50`, a conditional interval `[3/7, 6/7]`, robust at a low
threshold and sensitive at a high one (`robust_at_low_threshold`,
`sensitive_at_high_threshold`). `Sqrt2Branch.lean` carries the provenance:
the irrationality argument is a `sqrt2_dependency_chain` of explicit steps,
and a contradiction at one step does not explode the rest
(`sqrt2_chain_contradiction_step`, with `Branches.lean` giving the
no-explosion example `local_contradiction_no_explosion_example`).

Benchmark: a self-similar object gets a robustness verdict (interior versus
boundary), a numerical sensitivity interval, and a step-by-step provenance
chain that localizes any contradiction instead of trivializing the whole
construction.

## Stage 4: graded analysis (metric, continuity, differentiability, dimension)

Lean anchor: `Cred/Math/Metric.lean`, `Cred/Math/Continuity.lean`,
`Cred/Math/Smoothness.lean`, `Cred/Math/Dimension.lean`.

Classical asks: is a sequence convergent, is a function continuous at a
point, is it differentiable, what is the dimension of a self-similar set.
Each is a proposition or a single real.

Cred adds a threshold reading whose meet recovers the classical notion
exactly. Closeness `cClose x y = 1 - min(|x-y|,1)` reads distance as a
credence; `TLimit` and `TContinuousAt` hold at a threshold `t < 1` with a
band of radius `1-t`, and the meet over all thresholds is exact:
`tlimit_all_iff_tendsto` recovers Mathlib's `Tendsto`, and
`tcontinuousAt_all_iff_continuousAt` recovers `ContinuousAt` (globally
`tcontinuous_all_iff_continuous`). Differentiability is a predicate, so
`diffStatus` is two-valued, 1 exactly when `DifferentiableAt` holds
(`diffStatus_eq_one_iff`, `diffStatus_crisp`), with `|x|` at 0 the failure
witness (`diffStatus_abs_zero`). Dimension is sourced from the Moran
equation: for `n` maps of ratio `r`, `similarityDim n r = log n / log(1/r)`
is the unique solution of `n r^s = 1` (`moran_general`,
`moran_general_unique`), and the finite box estimate equals it at every
scale (`box_estimate_eq_dim`); the Cantor set is the instance `n=2, r=1/3`
(`cantor_is_instance`).

Benchmark: each analytic predicate has a graded threshold reading whose
crisp fragment is exactly the Mathlib notion; the only intrinsic degrees are
the boundary (exact) and the ordering, never a free-floating interior value.

## Stage 5: graded geometry (n-D manifold recovery present, superstructure future)

The graded manifold layer now recovers Mathlib's own smooth-manifold notion
in n dimensions; the differential-geometric superstructure above it is future.

- 1-D atlas seed: `Cred/Topology/Manifold.lean`. A `GradedChart` maps a carrier
  into the one-dimensional model `ℝ`; `transitionSmoothness τ` is 1 iff the
  supplied transition is `C^∞` (`transitionSmoothness_eq_one_iff`,
  `transitionSmoothness_comp`); `smooth_atlas_recovery` returns the transitions
  as genuine `ContDiff` maps at aggregate status 1.
- n-D recovery (real, not a seed): `Cred/Topology/ManifoldN.lean`. Over the
  Euclidean model `EuclideanSpace ℝ (Fin n)` with boundaryless `𝓘(ℝ, E)` and an
  abstract `[ChartedSpace E M]`, the per-transition status reads
  `contDiffGroupoid ∞` membership, and `atlasSmoothStatus_eq_one_iff_isManifold`
  proves `atlasSmoothStatus = 1 ↔ IsManifold (𝓘(ℝ,E)) ∞ M`, i.e. the graded
  status reaches certainty exactly when M is a Mathlib C^∞ manifold. Order `∞`
  is C^∞ (this Mathlib version places `⊤ = ω` analytic strictly above `∞`). The
  model space scores 1 (`atlasSmoothStatus_model_space`).
- Differential layer (real, not a seed): `Cred/Topology/Differential.lean`. For a
  map `f : M → M'` between Euclidean-model charted spaces,
  `mdiffStatus_eq_one_iff` proves `mdiffStatus f = 1 ↔ ContMDiff I I' ∞ f`; at
  status 1, `mdiffStatus_mdifferentiable` gives `MDifferentiable` so the
  pushforward `mfderiv f x` is the genuine tangent map `T_xM →L T_{fx}M'`
  (`mdiffStatus_mfderiv_isCLM`, with `mfderiv_id`/`mfderiv_const` restated), and
  `mdiffStatus_modelMap_eq_one_iff` bridges to ordinary `ContDiff ℝ ∞` on the
  model. id/const/composition closure proved.
- Tangent bundle layer (real, not a seed): `Cred/Topology/TangentBundleLayer.lean`.
  For a C^∞ manifold M over the model, `tangentBundleStatus_eq_one` recovers that
  the tangent bundle TM is a mathlib smooth manifold (`Bundle.TotalSpace.isManifold`),
  `tangentProjStatus_eq_one` that the bundle projection is C^∞ (`Bundle.contMDiff_proj`),
  and `zeroSectionStatus_eq_one` that the zero section is a smooth section
  (`Bundle.contMDiff_zeroSection`, `ContMDiffSection`); each with iff-recovery and
  a model-space corollary.
- Lie group layer (real, not a seed): `Cred/Topology/LieGroupLayer.lean`.
  `lieGroupStatus_eq_one_iff` / `lieAddGroupStatus_eq_one_iff` recover mathlib's
  `LieGroup` / `LieAddGroup`; the Euclidean additive group is a concrete witness
  (`lieAddGroupStatus_model_space`), with smooth addition (`groupAddStatus_eq_one`),
  negation (`groupNegStatus_eq_one`), and left/right translation
  (`leftAddTransStatus_eq_one`, `rightAddTransStatus_eq_one`) recovered. Distinct
  from `Cred/Approx/LieGroup.lean` (discrete-group-step preservation).
- Integral-curve / flow layer (real, not a seed): `Cred/Topology/IntegralCurveLayer.lean`.
  `integralCurveStatus_eq_one_iff` recovers mathlib's `IsIntegralCurve`;
  `integralCurve_exists` recovers Picard-Lindelof existence (CompleteSpace +
  boundaryless + C^∞ field); `integralCurve_unique` recovers uniqueness on a
  Hausdorff manifold; `constField_integralCurve_status` proves the explicit
  translation flow of a constant field on the model. Future: the global flow map
  (t,x) -> phi_t x, one-parameter groups, completeness, Hamiltonian dynamics.
- Hamiltonian flow capstone: `Cred/Topology/HamiltonianFlow.lean`. The harmonic
  oscillator H = (q^2+p^2)/2, field X_H = (p,-q): `oscillator_isIntegralCurve`
  (the rotation phase flow is a genuine integral curve), `oscillator_energy_conserved`
  (H constant along the orbit), `oscillator_flow_symplectic` (time-t map symplectic,
  det 1, via Cred.Approx). One worked system unifying the integral-curve, energy,
  and symplectic layers. NOT general Hamiltonian mechanics (abstract symplectic
  form, Hamilton's equations for general H, Poisson brackets, Liouville) -- those
  need symplectic-form infrastructure mathlib does not yet provide.
- Diffeomorphism layer (real, not a seed): `Cred/Topology/DiffeoLayer.lean`.
  `diffeoStatus_eq_one_iff` recovers a mathlib `Diffeomorph` witness (smooth iso),
  completing the smooth-map layer (ContMDiff = morphisms, Diffeomorph = isos):
  forward and inverse `ContMDiff` (`diffeoStatus_contMDiff`,
  `diffeoStatus_contMDiff_symm`), identity (`diffeoStatus_id`), continuous-linear-equiv
  witness (`clmDiffeoStatus_eq_one`), composition closure (`diffeoStatus_comp`).
- The recovery stops at mathlib's frontier. Differential forms, de Rham
  cohomology, connections, curvature, and integration on manifolds have NO
  mathlib target in this version, so a graded layer over them would be an
  unanchored seed; they are genuine future work, not asserted here. Likewise
  measure-theoretic (Hausdorff) dimension, per-orbit integrator preservation,
  and geometric-invariant robustness.
- Structure-preservation scores for geometric integrators: `future`. A
  per-step preservation credence for a symplectic or variational integrator
  over a trajectory, extending the single-step scores of Stage 2 to a score
  along an orbit, calibrated against energy and momentum drift.
- Robustness of geometric invariants: `future`. A robustness interval for a
  geometric invariant (curvature integral, holonomy, winding number) under
  perturbation of the metric or connection, extending Stage 3's interior
  versus boundary verdict from scalar conditioning to geometric quantities.

Each future item inherits the same contract: import the classical statement
from Mathlib, add the graded or robust layer above it, and prove that the
crisp or exact case collapses to the classical answer.

## Stage list

1. Graded sets and graded topology. Anchor: `Cred/Set`, `Cred/Topology`.
2. Structure-preserving numerics. Anchor: `Cred/Approx`.
3. Fractal and self-similarity status. Anchor: `Cred/Examples`,
   `Cred/Dependence/RobustCollapse.lean`.
4. Graded analysis: metric, continuity, differentiability, dimension.
   Anchor: `Cred/Math/{Metric,Continuity,Smoothness,Dimension}.lean`.
5. Graded geometry: n-D manifold recovery in `Cred/Topology/ManifoldN.lean`
   (atlas status = 1 iff mathlib C^∞ manifold), 1-D seed in
   `Cred/Topology/Manifold.lean`; tangent bundles, forms, de Rham, invariant
   robustness `future`.
