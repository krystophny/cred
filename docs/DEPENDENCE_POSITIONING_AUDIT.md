# Dependence positioning audit

This audit records the correction after the copula / fuzzy-logic discussion.

## Correct doctrine

Probability is not obtained by merely replacing `{0,1}` with `[0,1]`.  That move
gives many-valued semantics.  Probability also requires supplied joint/dependence
structure.

- A t-norm is a fixed scalar coupling policy.
- The product t-norm corresponds to independence when it is used as a joint:
  `J(A,B)=cred(A) cred(B)`.
- The min t-norm corresponds to maximum positive dependence / comonotone coupling
  when it is used as a joint.
- General probability does not choose one scalar function `R x R -> R` for all
  proposition pairs.  It supplies the joint on events/propositions.
- Cred's chain-rule kernel is `Adm(c;j,e) <-> c e = j`, which operates once the
  joint `j` has been supplied.

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
