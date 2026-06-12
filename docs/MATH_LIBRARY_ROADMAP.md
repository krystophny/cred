# Math library roadmap: ordinary mathematics inside Cred

Tracking issue: #592. Companion issues: #593 (Nat), #594 (reals), #595
(topology), #596 (statuses), #597 (metric/limits).

This is the plan for an ordinary-mathematics library inside the Cred foundation
language. It records what is already formalized in Lean, what mathematics is
standard and merely hosted, and what is roadmap. Read the status of each item
literally: formalized means `lake build` checks it today; planned means it does
not exist yet.

## Guiding principle

Classical mathematics embeds as the crisp fragment. A formula whose atoms all
take credence 0 or 1 evaluates exactly as it would in two-valued logic. The
embedding is `Cred.Bridge.embed : Bool → Credence` and the agreement is
`crisp_eval_eq` / `crisp_embedding` in `lean/Cred/Bridge/Crisp.lean`. On crisp
data, certainty consequence, positivity consequence, and classical consequence
coincide (`crisp_certainty_iff_classical`, `crisp_positivity_iff_classical`).

Cred adds status on top of the embedded theorem. The same statement can be:

- crisp classical, recovered with all atoms in `{0,1}`;
- graded, with atoms in the open interval and a credence-valued verdict;
- threshold-qualified, valid at level `t` but not at certainty
  (`thresholdConsequence t` in `lean/Cred/Threshold.lean`);
- branch-dependent, true in some admissible models and not others;
- underdetermined, where a conditioning constraint at zero evidence fixes a set
  of admissible values rather than one (`Cond`, `conditioning_zero_any`);
- non-explosive under contradiction: a contradictory branch does not derive an
  arbitrary conclusion (`labelled_no_ex_falso`, `lp_no_explosion`).

The classical theorem and its Cred status are separate facts. The roadmap keeps
them separate everywhere.

## Status vocabulary

Issue #596 fixes the convention; the planned `docs/THEOREM_STATUSES.md` is the
reference. Each library theorem carries one status header:

- **crisp** classical theorem recovered on `{0,1}` data;
- **certainty** consequence (verdict 1, the strongest graded form);
- **positivity** consequence (verdict above 0);
- **threshold** consequence at a stated level `t`;
- **branch-dependent**, holding on a subset of admissible models;
- **contradictory branch**, where premises clash but nothing explodes;
- **underdetermined/admissible**, where conditioning fixes a set;
- **robust**, holding across all admissible branches.

The crisp / certainty / positivity collapse is already proven on crisp data
(`crisp_positivity_iff_certainty`, `crisp_positivity_iff_classical`). The
remaining statuses are where Cred-specific content lives.

## Dependency order

```
Nat  ->  order / algebra  ->  rationals / reals  ->  metric / topology
```

Each layer reuses the crisp embedding and the threshold/admissibility machinery
from the layer below. Nat is the most developed; topology is a sketch.

## Layer 1: natural numbers (#593)

### Already formalized

`lean/Cred/Foundation/Arithmetic.lean` carries a standard `Nat` model
(`natModel`) with genuine `0`, successor, addition, and multiplication, crisp
equality (`natModel_crispEquality`), and inf/sup quantifiers
(`natModel_quantifierLaws`). The seven Robinson Q axioms are closed formulas and
evaluate to certainty on this model. Small examples (`0 = 0`, an add-zero
instance, `2 + 1 = 3`) are checkable proof certificates.

The arithmetic terms are `ArithQTerm` (`zeroT`, `succT`, `addT`, `mulT`); the
formulas are `ArithQFormula`.

### First target theorems

- **crisp**: numeral equalities and apartness at certainty, e.g.
  `natModel.eval (3 = 3) = 1` and `natModel.eval (succ 0 = 0) = 0`, extending the
  current `2 + 1 = 3` example to a numeral table.
- **crisp**: order, defined arithmetically (`a <= b` as `exists k, a + k = b`),
  reflexivity and transitivity at certainty.
- **crisp**: commutativity and associativity of `+` over numerals, as
  certainty-evaluated closed instances (model facts, not an internal induction
  schema).
- **branch-dependent**: an optional arithmetic axiom (for instance a stipulated
  bound) tracked as a branch, certain in the branch that asserts it and
  unconstrained otherwise.
- **threshold**: a graded arithmetic atom (a predicate read off a non-crisp
  credence) that is positive but not certain, to exercise
  `thresholdConsequence`.

### Open design choice

How much induction: none, an external schema over `Nat`, or an internal
induction fragment in the object language. The current model proves universally
quantified facts through the real inf quantifier ranging over all of `Nat`, so
many `forall` statements are already certainty facts without an internal schema.
Decide before extending past Q.

## Layer 2: order and algebra

### Already formalized

The value algebra itself is the worked algebraic object. `lean/Cred/Algebra.lean`
abstracts the credence value algebra; `lean/Cred/Algebra/Rational.lean` builds it
on the rational unit interval, off the reals. `lean/Cred/Algebra/Finite.lean`
carries the finite case. The order, negation, product conjunction, and De Morgan
disjunction live in `lean/Cred/Core/Value.lean`.

### First target theorems

- **crisp**: ordered-monoid laws for `Nat` addition and multiplication, lifted
  from Layer 1, stated as certainty consequences.
- **graded**: monotonicity of `⊗` and `⊔` in each argument on `[0,1]`, reused
  from the value algebra.
- **underdetermined**: the conditioning trichotomy as an order fact, `Cond j e`
  is a singleton for `e > 0`, a full interval for `j = e = 0`, and empty
  otherwise (`cond_singleton_of_pos`, `cond_zero_zero_univ`, `cond_nonempty_iff`
  in `lean/Cred/Cond/Admissible.lean`).

This layer is mostly a re-export and statement-shaping layer over existing
algebra; little new mathematics is needed.

## Layer 3: rationals and reals (#594)

### Already formalized

`lean/Cred/Algebra/Rational.lean` is the rational unit interval as a value
algebra. `lean/Cred/Algebra/Completion.lean` completes it to the hosted interval:
`rat_dense_in_credence` gives density of rationals in `Credence`, and
`value_algebra_complete` gives quantifier completeness reused from mathlib. The
executable checker stays real-free (`Foundation/CheckBool.lean`), so the reals
are a semantic convenience, not part of the runtime trusted base.

### Design boundary to keep explicit

Three roles for the reals, and the boundary between them is load-bearing:

- hosted `ℝ` (mathlib) as the semantic domain for analysis facts;
- the rational/finitary value algebra for the executable checker;
- the completion (`Algebra/Completion.lean`) as the bridge between them.

A real-number fact is either imported from mathlib or an object-language Cred
fact. The library must label which. Issue #594 calls for `docs/REALS_IN_CRED.md`
to fix this.

### First target theorems

- **crisp**: order reflexivity, additive identity, multiplicative identity, and
  one simple strict inequality on `ℝ`, recovered as certainty consequences on
  crisp atoms.
- **graded**: a credence-valued comparison atom whose verdict sits in the open
  interval, to show the same inequality carrying status.
- **admissible**: a limiting ratio near a zero denominator represented as an
  admissible set via `Cond`, not a forced value. This is the analysis face of
  `conditioning_zero_any`: division by zero is underdetermination, not error.
- **branch-dependent**: a completeness- or choice-flavored real-number claim
  tracked as a branch, with the trusted-base audit (`Branch/AxiomAudit.lean`)
  recording its axiom dependence.

## Layer 4: metric and limits (#597)

### Planned

No metric module exists yet. The plan bridges reals to topology.

- define a metric-space signature, or host mathlib's metric spaces as semantic
  structures;
- define convergence and a Cauchy predicate, either in the foundation language
  or as semantic structures over the hosted reals;
- separate crisp convergence (the classical statement) from threshold
  convergence (above level `t` before certainty);
- a boundary example where a limiting constraint degenerates and becomes
  underdetermined, modeled as an admissible set rather than a forced limit.

### First target theorems

- **crisp**: a convergent sequence has its classical limit at certainty.
- **threshold**: a sequence whose terms are positive past an index, certain only
  in the limit, exercising `thresholdConsequence` along the index.
- **admissible**: a zero-denominator limiting case as an admissible set, reusing
  the `Cond` trichotomy.
- **branch-dependent**: a limit whose value differs across admissible model
  branches.

Issue #597 calls for `docs/METRIC_LIMITS_IN_CRED.md` with at least one formal or
semi-formal example.

## Layer 5: topology (#595)

### Planned

No topology module exists yet. Three tracks:

- **crisp topology**: a topological space as a family of open predicates or
  `CredSet`s, with ordinary open sets embedding through the crisp fragment;
  continuity as preimages of open sets.
- **graded topology**: open membership is credence-valued; closure and interior
  through sup and inf, reusing the `CredSet` operations in
  `lean/Cred/Set/Basic.lean` (`union` as sup, `inter` as product, `compl` as
  negation).
- **branch-aware topology**: claims depending on separation axioms or
  compactness tracked as branches, classified robust, branch-dependent,
  contradictory, or underdetermined.

### First target theorems

- **crisp**: ordinary open sets embed; a finite intersection of open sets is
  open, recovered on crisp `CredSet`s.
- **threshold**: alpha-cut topology. The `t`-open sets (membership at or above
  `t`) form the threshold analogue, read directly off `thresholdConsequence`.
- **graded**: graded closure and interior via sup/inf, compared against the
  crisp closure on crisp data.
- **branch-dependent**: a separation-axiom-dependent claim, certain in the
  branch that assumes the axiom.

Issue #595 calls for `docs/TOPOLOGY_IN_CRED.md` with at least one crisp theorem
and one genuinely graded example.

## Cross-links

- Foundation language and semantics: `lean/Cred/Foundation/Language.lean`,
  `lean/Cred/Foundation/Semantics.lean`.
- Crisp embedding and the classical/certainty/positivity collapse:
  `lean/Cred/Bridge/Crisp.lean`.
- Value algebra and its rational/finite constructions, plus the completion:
  `lean/Cred/Algebra.lean`, `lean/Cred/Algebra/Rational.lean`,
  `lean/Cred/Algebra/Finite.lean`, `lean/Cred/Algebra/Completion.lean`.
- Admissible conditioning and the trichotomy: `lean/Cred/Cond/Admissible.lean`.
- Threshold consequence: `lean/Cred/Threshold.lean`.
- Graded set theory used for topology membership: `lean/Cred/Set/Basic.lean`,
  `lean/Cred/Set/Classical.lean`.
- Arithmetic seed: `lean/Cred/Foundation/Arithmetic.lean`.
- Axiom audit for branch tracking: `lean/Cred/Branch/AxiomAudit.lean`.

## Acceptance check against #592

- The roadmap exists at `docs/MATH_LIBRARY_ROADMAP.md`.
- Dependency order is stated: Nat, order/algebra, rationals/reals,
  metric/topology.
- Each area distinguishes crisp, graded, branch-dependent, and
  admissible/underdetermined theorems, with at least three first targets.
- Formalized layers (Nat seed, value algebra, rationals, completion) are
  separated from planned layers (metric, topology) explicitly.
