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

## Stage 4: graded geometry (future)

No Lean anchor yet. This stage names the targets the earlier stages build
toward.

- Graded manifold and atlas status: `future`. A chart membership credence
  and an atlas-coverage degree on top of Mathlib's `ChartedSpace`, with the
  crisp collapse recovering the classical atlas. Stage 1's graded openness
  and threshold cuts are the intended starting point.
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
4. Graded geometry: manifold and atlas status, integrator preservation
   scores, invariant robustness. `future`.
