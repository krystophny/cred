# Structure-preserving approximation: roadmap

Umbrella roadmap for the Cred structure-preservation track. Tracks issues #609
(umbrella), #610 (literature map), #628 (comparison table), #630 (implementation
order).

Status: the generic interface in `lean/Cred/Approx/Structure.lean` is drafted, but
the module does not yet build. Two proofs fail under `lake build`:
`crispScore_zero_iff` (field notation on `heq`) and
`exactPreserves_iff_preservesAt_one` (`no goals to be solved`). The file is
untracked. Every comparison row and every ladder stage below is planned, not yet
formalized. Sections flag which is which.

## 1. Thesis

An approximation is judged on two axes. The first is value error: how far the
computed value sits from the exact one. The second is structure: whether the
approximation keeps the defining property of the object it approximates.

Examples of a defining property: positivity of a density, mass conservation,
a maximum principle, norm preservation under a rotation, a divergence-free
constraint, the symplectic form of a Hamiltonian flow, the bar-code of a
filtration.

A scheme can be accurate in value and still destroy structure. Explicit Euler on
a linear oscillator drifts in energy and grows the norm; its local value error is
order one in the step, but the invariant it should keep fails. The two failures
are different and want different bookkeeping.

Cred records structure failure as a status, not as added value error. A scheme
that breaks the defining property gets an inadmissible status or a low structure
degree. It does not get a larger error number. Value error and structure degree
are separate columns.

Claim, stated explicitly per #628: Cred supplies a uniform status language for
comparing value accuracy against structural admissibility. It does not invent
structure preservation. Symplectic integration, positivity-preserving schemes,
mimetic discretization, and persistent homology already preserve structure and
already prove they do. The contribution here is the shared status vocabulary that
lets these be tabulated and compared on one scale, with the no-ex-falso /
admissible-conditioning machinery of Cred behind the status grade.

## 2. Literature map

Established mathematics. Each line is an anchor, not a survey. Full citations
belong in `docs/STRUCTURE_PRESERVING_LITERATURE.md` (issue #610, not yet
written).

- Geometric / symplectic integration. Hairer, Lubich, Wanner, *Geometric
  Numerical Integration*: long-time behavior follows from preserving the
  symplectic form, not from small local error.
- Variational integrators. Marsden and West: discretize the action, derive the
  scheme from a discrete Euler-Lagrange equation, inherit momentum conservation
  and a discrete symplectic form.
- Lie group integrators. Munthe-Kaas, Iserles: keep the numerical flow on the
  manifold (a Lie group or homogeneous space) instead of stepping off it in the
  ambient space.
- SSP / positivity-preserving schemes. Strong-stability-preserving time
  integration and positivity limiters keep densities and probabilities
  nonnegative under explicit steps.
- Discrete-gradient / energy-preserving methods. Replace the gradient by a
  discrete gradient so the one-step map conserves a first integral exactly.
- Finite-volume conservative methods. Telescoping numerical fluxes make the
  discrete update conserve the integrated quantity cell by cell.
- Mimetic / DEC / FEEC. Discrete exterior calculus and finite element exterior
  calculus reproduce `d∘d = 0` and Stokes at the discrete level, so the discrete
  de Rham complex is exact.
- Persistent homology / TDA. The persistence diagram is a structural summary of a
  filtration; the stability theorem bounds diagram distance by input
  perturbation, so the topological summary is itself an approximation with a
  preservation guarantee.

These are mature results in their own literatures. Cred reinterprets none of the
mathematics. It reads each guarantee as a structure-degree statement.

## 3. The Cred vocabulary

Defined in `lean/Cred/Approx/Structure.lean` (drafted, see Status; two proofs
still fail). A structure on a carrier `X` is a credence-valued score
`P : X → Credence`. The score reuses the core value
algebra (`Cred/Core/Value.lean`): `0` is total failure, `1` is exact
preservation, interior values are graded.

- `StructureDegree P x` is the score `P x`. The grade of structure that `x`
  carries.
- `ExactPreserves P x` is `StructureDegree P x = 1`. The defining property holds
  exactly.
- `PreservesAt t P x` is `t ≤ StructureDegree P x`. The structure is kept to at
  least threshold `t`.
- `AdmissibleApprox t P x` is `PreservesAt t P x`. An approximation counts as
  admissible at threshold `t` when its degree clears `t`.
- `crispScore P` lifts a decidable predicate to a `0/1` score, so a classical
  on/off structure embeds as the boundary case
  (`exactPreserves_crispScore : ExactPreserves (crispScore P) x ↔ P x`).
- `Preserves P Φ` says a self-map `Φ : X → X` keeps the exact-preservation class:
  if `x` preserves exactly, so does `Φ x`.

Generic facts stated in the module: `preservesAt_zero` (the zero threshold is
free), `exactPreserves_iff_preservesAt_one` (exactness is preservation at the top
threshold; this proof currently fails), `preservesAt_mono` (lower thresholds are
easier), `preserves_id` and `preserves_comp` (the preserving schemes contain the
identity and are closed under composition).

The threshold `t` is the admissibility knob. Setting `t = 1` demands exact
structure; lowering `t` admits graded preservation. This is the single status
scale the comparison table reads off.

## 4. Comparison table format

Per #628. Columns: method, order / error, preserved structure, structure degree,
status, admissibility condition.

- Method: the scheme.
- Order / error: value-accuracy column. Local or global order in the step size.
- Preserved structure: the defining property `P` at stake.
- Structure degree: `StructureDegree P x` for the scheme's output, exact or
  graded.
- Status: admissible or inadmissible at the chosen threshold `t`.
- Admissibility condition: the hypothesis under which the status holds (step-size
  bound, parameter range, model assumption).

Placeholder rows for the minimal examples (#612-616). None of these rows is
formalized yet; the values are the targets the example modules must hit.

| Method | Order / error | Preserved structure | Structure degree | Status | Admissibility condition |
|---|---|---|---|---|---|
| Explicit Euler, scalar decay | local order 2 | positivity (`x ≥ 0`) | exact iff step small | admissible / inadmissible | `h ≤ 1/λ` (planned, #612) |
| Implicit Euler, scalar decay | local order 2 | positivity (`x ≥ 0`) | exact, all steps | admissible | unconditional (planned, #612) |
| Normalized update, simplex | order TBD | simplex (`∑ = 1`, `≥ 0`) | exact | admissible | normalization applied (planned, #613) |
| Linear interpolation | order 2 | monotonicity | exact | admissible | monotone nodes (planned, #614) |
| Explicit Euler, rotation | local order 2 | norm (`‖x‖` fixed) | graded, drifts | inadmissible at `t=1` | none keeps it exact (planned, #616) |
| Symplectic Euler, rotation | local order 2 | symplectic form | exact | admissible | (planned, #619) |

The row pattern is the deliverable; the entries become real as the example
modules land.

## 5. Implementation order

Per #630. The #612-626 ladder, simplest structure first, differential geometry
and PDE last. Status: stage 0 (the generic interface) is formalized; stages 1
onward are planned, with no example module written yet.

Stage 0. Generic structure-degree interface. `Cred/Approx/Structure.lean`.
Drafted, two proofs failing (see Status above); fix and commit before the
example modules import it.

Minimal examples (short-term, #612-616):

1. Positivity-preserving scalar ODE. #612.
2. Probability-simplex preservation. #613.
3. Monotonicity-preserving interpolation. #614.
4. Maximum-principle preservation. #615.
5. Norm / circle preservation. #616.

ODE track (#617-621):

6. Invariant-preserving one-step maps. #617.
7. First-integral-preserving methods (discrete gradient). #618.
8. Symplectic integrators for Hamiltonian systems. #619.
9. Variational integrators, discrete action principle. #620.
10. Lie group integrators. #621.

PDE and geometry track (#622-625, long-term):

11. Finite-volume conservation, telescoping fluxes. #622.
12. Positivity / SSP / entropy status for PDE. #623.
13. Compatible discretizations (mimetic / DEC / FEEC). #624.
14. Divergence-free and constraint-preserving schemes. #625.

Data / topology track (#626, long-term):

15. Persistent homology as a structural degree. #626.

Acceptance for the umbrella (#609): the roadmap exists (this file), at least one
minimal finite example and one ODE example are fully formalized, later stages
scoped. The two formalized examples are the next deliverables; today only the
generic interface compiles.

The dependency is linear in spirit. Each minimal example fixes one structure `P`
and one scheme, instantiates `StructureDegree` / `AdmissibleApprox`, and proves
the admissibility condition in its row. The ODE and PDE stages reuse that
interface; they add the geometry, not new vocabulary.
