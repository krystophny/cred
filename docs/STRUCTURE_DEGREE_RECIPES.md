# Structure-degree recipes

A structure degree is a credence in `[0,1]` that grades how well a numerical
state keeps a structure. To stop the grades from being arbitrary numbers, every
degree in `Cred/Approx/` must come from a fixed recipe. This document states the
recipe and lists the residual, scale, and score for each example.

## The recipe

A structure degree is specified by six choices.

1. An exact structural predicate or equation `P(x)`.
2. A residual `r_P(x) >= 0` that is zero exactly when `P(x)` holds.
3. A norm or aggregation rule when `r_P` has several components.
4. A scale `eps > 0` with a documented origin (a tolerance, a step bound, a grid size).
5. A deterministic map `score_eps : [0, inf) -> [0,1]`.
6. A threshold `t` when a crisp status is extracted.

## Default score

Use the clipped-linear score unless a domain reason forces another:

```text
score_eps(r) = max(0, min(1, 1 - r/eps))
StructureDegree_{P,eps}(x) = score_eps(r_P(x))
```

A zero residual scores `1` (exact structure), a residual at or past `eps` scores
`0`, and the score is antitone in the residual. The score lives in
`Cred/Approx/Score.lean` as `scoreEps eps r`, with the bounds and
characterizations proved once:

- `scoreEps_nonneg`, `scoreEps_le_one`: the score is a credence in `[0,1]`.
- `scoreEps_one_of_zero`, `scoreEps_eq_one_iff`: for `eps > 0` and `r >= 0`, the
  score is `1` exactly when `r = 0`.
- `scoreEps_zero_of_ge`: residuals at or past `eps` score `0`.
- `scoreEps_antitone`: larger residuals score lower.
- `scoreEpsCredence`, `scoreEpsCredence_one_of_zero`, `scoreEpsCredence_zero_of_ge`:
  the same score packaged as a `Credence`.

Crisp on/off structures are the boundary case: their residual is `0` or `1` and
the score collapses to `crispScore`, so `exactPreserves_crispScore` reads the
predicate back off the degree.

## Residual, scale, and score per example

| Structure | Predicate `P` | Residual `r_P` | Module |
|---|---|---|---|
| Positivity | `0 <= y` | `max(0, -y)` | `Approx/Positivity.lean`, `Approx/SSP.lean` |
| Mass conservation | `sum p = m` | `\|sum p - m\|` | `Approx/FiniteVolume.lean` |
| Simplex | nonnegative, unit mass | mass residual plus negativity residual | `Approx/Simplex.lean` |
| Norm / circle | `\|\|x\|\|^2 = 1` | `\| \|\|x\|\|^2 - 1 \|` | `Approx/NormCircle.lean` |
| Unit group | `normSq z = 1` | `\| normSq z - 1 \|` | `Approx/LieGroup.lean` |
| Symplecticity | `Aᵀ J A = J` | `\|\| Aᵀ J A - J \|\|` | `Approx/Symplectic.lean` |
| Divergence-free | `div_h u = 0` | `\|\| div_h u \|\|` | `Approx/DivFree.lean` |
| Compatibility | `d1 . d0 = 0` | `\|\| d1 (d0 u) \|\|` | `Approx/Compatible.lean` |
| Energy balance | `E(next) = E - diss + in` | `\| E(next) - E + diss - in \|` | `Approx/EnergyBalance.lean` |
| Persistence | feature length `>= eps` | `max(0, eps - (death - birth))` | `Approx/Persistence.lean` |

The residual is what the score consumes. For a crisp example the score is `0` or
`1`; for a graded example the score interpolates by the recipe above.

## A worked numeric table

Positivity of a scalar at scale `eps = 1`, residual `r(y) = max(0, -y)`:

| `y` | `r(y)` | `score_1(r)` | status at `t = 1/2` |
|---|---|---|---|
| `0.5` | `0` | `1` | admissible |
| `0` | `0` | `1` | admissible |
| `-0.25` | `0.25` | `0.75` | admissible |
| `-0.5` | `0.5` | `0.5` | admissible (boundary) |
| `-0.75` | `0.75` | `0.25` | inadmissible |
| `-1` | `1` | `0` | inadmissible |

The numbers are deterministic: fix `eps` and the residual and the score follows.
The threshold `t` is the only place a crisp verdict enters, and it is named, not
implicit.

## Rule for new examples

Any new `Approx` example states its `P`, its residual `r_P`, its scale `eps` with
a documented origin, and uses `scoreEps` (or justifies a different score in one
line). A structure degree without a residual and a scale is not admitted.
