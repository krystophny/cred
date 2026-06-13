# New single-paper sections

This directory contains manuscript-ready sections produced after the Priest/material-conditional discussion.

Recommended insertion in `singlepaper/paper.tex`:

```tex
\input{sections/pointwise_truth_connection}
\input{sections/proof_patterns}
\input{sections/probability_as_dependence_logic}
```

Place `pointwise_truth_connection` after `Contribution Hierarchy` and before `The Setting`. Place `proof_patterns` after `Proof Theory`, or keep it near the front if the paper needs stronger proof-method positioning. Place `probability_as_dependence_logic` after `Pointwise Truth Is Not Connection` or in `Relation to Existing Work`, depending on whether the submission should emphasize conceptual novelty or literature positioning.

Core positioning:

- Do not claim that Cred uniquely discovers the distinction between truth and entailment; classical model theory already has that.
- Claim the narrower advantage: Cred keeps value, consequence, supplied dependence, and conditioning as separate interfaces.
- The probability analogy is central: marginals do not determine the joint; truth values do not determine a connection.
- Zero evidence is underdetermination, not vacuous truth and not explosion.
- Probability-as-logic should be stated as dependence-enriched logic: fuzzy truth values alone are not enough; one must free the joint from truth-functionality and supply dependence data.
