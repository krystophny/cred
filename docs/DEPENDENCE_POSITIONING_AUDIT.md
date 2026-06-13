# Dependence positioning audit

This audit records the correction after the copula / fuzzy-logic discussion.

## Correct doctrine

Probability is not fuzzy logic with numbers.  Replacing `{0,1}` with `[0,1]` gives
many-valued semantics; probability is logic plus dependence.  Fuzzy logic
generalizes classical logic by grading truth values.  Cred additionally generalizes
the joint, keeping it as supplied structure rather than fixing it by a truth
function.

- The joint `j = cred(A and B)` is supplied dependence data, never a value function
  of the marginals.  `cred(A)` and `cred(B)` do not determine it.
- A t-norm is one fixed scalar coupling policy, not the general joint.
- The product t-norm picks independence when used as a joint: `j = cred(A) cred(B)`.
- The min t-norm picks maximum positive dependence / comonotone coupling.
- A general joint is any point of the Fréchet interval
  `[max(cred(A)+cred(B)-1,0), min(cred(A),cred(B))]`, fixed by the
  propositions, not by their scalar values.  Probability does not choose one
  scalar function `R x R -> R` for all proposition pairs.
- Cred's chain-rule kernel is `Adm(c;j,e) <-> c e = j`, the interface that consumes
  the supplied joint and returns the admissible conditional.
- Honesty: Cred does not subsume probability or fuzzy logic.  It factors out the
  shared conditioning core and proves where each tradition commits to something
  extra: a measure; a truth-functional conditional plus ex falso; a designation
  policy.

## Corrected files

- `README.md`: added a dependence-discipline section and changed the primitives
  comment so product conjunction is not read as a universal joint.
- `lean/Cred/Cond/Copula.lean`: revised module comments and theorem comments so
  the min-copula uniqueness result is explicitly a truth-functionality boundary,
  not a statement that general copulas collapse to min.
- `docs/THEOREM_INVENTORY.md`: changed the Part 2 theorem row from a vague
  min-copula claim to the precise statement: truth-functional idempotent scalar
  joint is forced to min under copula-like assumptions; general probability must
  supply event-specific joints.
- `docs/SUBMISSION.md`: added cross-series submission guardrail: fuzzy truth values
  alone are not probability; probability is dependence-enriched logic.
- `docs/MILESTONES.md`: added dependence/joint separation to the formalized core and
  positioning guardrails.
- `singlepaper/sections/probability_as_dependence_logic.tex`: added a manuscript
  section stating the revised probability-as-logic hierarchy.

## Large paper passages to integrate

The older part papers contain wording that should be updated in the next full
manuscript pass.  The risky patterns are:

1. "Probability theory and many-valued logic share the same core algebra".
   Replace with: "They share scalar operations in important boundary cases, but
   probability carries event-specific joint/dependence structure."

2. "They differ only in the conditional".
   Replace with: "They differ in the conditional and in how the joint is supplied:
   fuzzy logic fixes a truth-functional joint, while probability supplies a
   dependence structure."

3. "Min copula uniqueness" without the truth-functionality caveat.
   Replace with: "Min is forced only for a single idempotent scalar truth-function
   satisfying the stated copula-like assumptions.  General probabilistic copulas are
   not ruled out."

4. "No intermediate copula".
   Replace with: "No intermediate truth-functional idempotent scalar joint under
   the stated assumptions.  Probability-style intermediate dependence is represented
   by supplied joints/copulas, not by one universal truth function."

5. "Probability as foundation/generalization of logic".
   Replace with: "Probability can be seen as dependence-enriched logic: crisp or
   graded values plus measure and supplied dependence.  Fuzzy truth values alone are
   insufficient."

## Review checklist additions

A reviewer should be able to verify that every occurrence of `copula`, `t-norm`,
`fuzzy`, `probability bridge`, and `truth-functional joint` obeys these rules:

- Does the text distinguish scalar value operations from proposition/event joints?
- Does it avoid saying that product conjunction is the general joint?
- Does it state that min uniqueness is conditional on truth-functionality and
  idempotence?
- Does it avoid implying that fuzzy logic alone gives probability?
- Does it identify the supplied joint as the probability-side dependence input?
