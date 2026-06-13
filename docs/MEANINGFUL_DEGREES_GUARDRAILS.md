# Meaningful-degrees guardrails

This governs the graded-structure section of the flagship paper. Every degree
in `[0,1]` that appears in the paper must be traceable to a named source. The
source fixes the mathematical form, the meaning, and the validity requirement
the degree must meet before it is used.

## The rule

A degree with no named source is not allowed in the paper. Before a number in
`[0,1]` enters as a credence, membership, score, radius, interval bound, or
expectation, classify it by one row of the table below and check its validity
requirement. A degree that fails its requirement, or that matches no row, does
not go in.

## Classification table

| Degree source | Mathematical form | Meaning | Validity requirement | Example |
|---|---|---|---|---|
| Crisp predicate embedding | `chi_P(x) in {0,1}` | exact truth value of a sharp predicate | `P` decidable on its domain; output is `0` or `1`, never interior | `chi_{prime}(7) = 1` |
| Fuzzy membership | `mu_A(x) in [0,1]` | degree to which `x` belongs to a graded set `A` | `mu_A` total on the domain with a stated defining function | `mu_{tall}(180 cm) = 0.7` |
| Residual-to-score recipe | `score_eps(r) = max(0, min(1, 1 - r/eps))` | how close a state is to satisfying `P`, on a named scale | residual `r >= 0` zero iff `P` holds; scale `eps > 0` has a documented origin; uses `scoreEps` | `score_1(0.25) = 0.75` for positivity residual `r(y)=max(0,-y)` |
| Robustness radius | `rho(x) = sup { delta : verdict stable on ball(x, delta) }` | largest perturbation that leaves the verdict unchanged | metric on the state space fixed; verdict well defined on the ball; `rho` reported with its metric | `rho = 0.05` under the sup norm |
| Admissible interval or fiber | `Cond(e, j) = { c : c (X) e = j }` | the set of conditional credences consistent with chain-rule data | follows the singleton / full-interval / empty trichotomy; no value read off a `0`-evidence fiber as if pinned | `Cond(0.5, 0.25) = {0.5}` |
| Measure or expectation | `mu(S) in [0,1]` or `E[f] in [0,1]` | probability mass of an event, or mean of an `[0,1]`-valued function | `mu` a normalized measure on a stated sigma-algebra; `f` measurable with range in `[0,1]` | `E[chi_S] = mu(S) = 0.3` |

## Reading the table

The first two rows are inputs: a crisp predicate gives a sharp `0` or `1`, a
fuzzy set gives a graded membership with its own defining function. The
residual-to-score row is the only general manufacturing recipe; it turns a
distance from a structure into a credence on a named scale, and it is the
subject of `STRUCTURE_DEGREE_RECIPES.md`. The robustness radius reports
stability, not membership, so it carries a metric. The admissible interval
comes from conditioning and obeys the trichotomy: a `0`-evidence fiber is the
full interval, and no single value may be quoted from it as determined. The
last row is the probabilistic source: a measure or an expectation of an
`[0,1]`-valued function.

Two failure modes the rule blocks. A bare constant with no recipe, residual, or
measure behind it: rejected, no source. A value lifted from a `0`-evidence
admissible interval and quoted as if pinned: rejected, the fiber is the whole
interval, so the value is not determined.
