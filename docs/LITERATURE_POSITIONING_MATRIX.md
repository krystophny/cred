# Literature positioning matrix

Where Cred sits against neighbouring traditions, for adversarial review. Each row
names a tradition, what Cred takes from it, where Cred differs, the Lean anchor (if
the difference is formalized), the paper location, and the overclaim risk to watch.

Cred's value carrier `[0,1]` carries several distinct layers: a many-valued truth
degree, `forall`-over-valuations consequence with a designation policy, supplied
dependence (the joint), the admissible-conditioning fiber `Cond(j,e)={c | c⊗e=j}`,
and an optional measure over valuations giving probability or imprecise probability.
The positioning below is layer-specific; conflating layers is the main review risk.

| Tradition | Known ingredient | Cred uses | Cred differs by | Lean anchor | Paper | Overclaim risk |
|---|---|---|---|---|---|---|
| Mathematical fuzzy / t-norm logic | graded truth values on `[0,1]`, t-norm conjunction | the product De Morgan triplet as the value layer | the conjunction is not the joint of two propositions; the joint is supplied | `Cred.Credence.conj_*`, `Cond/Copula.lean` | Setting; Relation to Existing Work | claiming Cred is "better fuzzy logic" |
| Product logic + residuum | residuated implication `e→j` | the product t-norm values | no internal conditional; conditioning is the external fiber, and the residuum reintroduces ex falso at `e=0` | `residuum_vs_fiber` (target), `curry_block` | Why the Conditional Must Stay External | implying the residuum and the fiber agree |
| Gödel / Łukasiewicz logics | min and bounded-sum t-norms as value algebras | optional value-algebra instances of the forall layer | not Cred's native carrier; included only as host-framework specializations | `Cred.Aggregation.Specializations` (target) | Forall consequence | claiming these logics are new |
| Kleene / LP / K3 / RM3 | three-valued designations | the collapse to `{0,½,1}` | the exact formula-level bridge: LP is positivity, K3 is certainty | `lp_formula_bridge`, `k3_formula_bridge` | The Kleene Collapse | claiming the bridge extends to conditioning (it does not) |
| Probabilistic logic over possible worlds | a measure over valuations | a finite measure layer over valuations | `forall` is the all-measures, verdict-one corner of the measure | `entails_iff_cond_one`, `entails_iff_dominated` | Probability over valuations | claiming the measure-theoretic continuum is formalized (only finite is) |
| Cox / Jaynes probability-as-logic | probability as the consistent extension of Boolean logic | a conservative finite representation | only the finite additivity-implies-measure direction is proved, not the full Cox functional-equation derivation | `cox_finite_representation` (target) | (comparison) | claiming "Cred proves Cox/Jaynes" |
| Imprecise probability / credal sets | sets of measures, lower and upper probability | a finite credal family with lower and upper probability | the credal set arises as the fiber of a supplied-joint interval, not as prior ignorance | `lowerP`, `upperP` (target), `RobustStatus` | Probability over valuations; robust collapse | conflating Cred with Walley's full theory |
| de Finetti conditionals / conditional events | void antecedent: a bet on a false condition is called off | the same zero-evidence behaviour | conditioning is a scalar fiber, not a three-valued conditional event; no compound-conditional algebra | `cond_zero_zero_univ`, `zero_evidence_duality` | Conditioning as a Relation | claiming Cred is a conditional-event algebra |
| Conditional random quantities | conditional gambles, coherence | the chain-rule constraint `c⊗e=j` | a single scalar invariant under those ingredients, not a full coherence calculus | `Cond/Admissible.lean` | Relation to Existing Work | overstating coherence-theoretic content |
| Paraconsistent no-explosion | gluts without trivialization | no ex falso at the positivity threshold and at zero evidence | non-explosion is semantic (surviving countermodel / full fiber), not relevance/aboutness tracking | `graded_no_explosion`, `labelled_no_ex_falso` | Threshold Consequence; Zero Evidence | claiming Cred is a relevance logic |

## Reviewer questions, answered

- **Is Cred just product fuzzy logic?** No. Fuzzy logic fixes the joint by a truth
  function and internalizes the conditional as a residuum; Cred supplies the joint
  and keeps conditioning external. The no-truth-functional-conditional-bridge theorem
  and the Curry block make the difference formal, not stylistic.
- **Is Cred just probability over possible worlds?** No. Cred's core has no measure on
  valuations; entailment is `forall`, not an integral. A measure is an optional layer,
  and `forall` is exactly its all-measures, verdict-one corner.
- **Is Cred just imprecise probability?** No. The credal set is the fiber of one
  supplied-joint interval; its width records loss of constraint, not subjective
  indecision.
- **Is Cred just de Finetti conditionals?** No. The void antecedent is shared, but
  conditioning is a scalar fiber, with no conditional-event truth table and no
  compound-conditional algebra.

## Honest limits

- Continuum / measure-theoretic probability is not formalized; only finite measures.
- The Cox/Jaynes connection is the conservative finite representation only.
- The Gödel and Łukasiewicz specializations are host-framework witnesses, not new logics.
- "Target" anchors are theorem goals in progress; see `CLAIM_STATUS.md` for status.
