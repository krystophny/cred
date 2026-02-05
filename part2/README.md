# Part 2: From Algebra to Reasoning

Part 1 establishes Cred as a constraint algebra on [0,1]: values, complement, product, De Morgan dual, and the chain rule for conditioning. It deliberately provides no interpretation, no consequence relation, and no update rule.

Part 2 adds these three layers, one at a time, and extends to first-order.

## Paper

`paper.tex` — publication paper covering valuations, consequence relations, update rules, and graded predicates. All named claims cross-reference machine-checked Lean theorems.

## Lean Formalization

| File | Contents |
|------|----------|
| `Cred/Valuation.lean` | Complement-preserving, independent, and joint valuations; collapse composition; Fréchet bounds |
| `Cred/Consequence.lean` | K3/LP designated values; three-valued and graded consequence; no-explosion theorems |
| `Cred/Update.lean` | Bayesian and Jeffrey conditionalization; chain-rule preservation; zero-evidence underdetermination |
| `Cred/Predicate.lean` | Graded predicates; pointwise operations; inf/sup quantifiers; quantifier duality; Russell fixed point |

## Notes

- `05-open-questions.md` — Research directions for Part 2

## Relationship to Part 1

Part 1 (conclusion, "What Cred provides and what it does not") identifies three missing layers:

| Layer | Part 1 status | Part 2 goal |
|-------|---------------|-------------|
| Interpretation | None (algebra only) | Cred valuations |
| Consequence relation | None | Graded entailment |
| Update rule | None | Conditionalization |

Each layer adds exactly the structure that the algebra leaves open. Different choices at each layer yield different systems (probability, K3, LP, RM3, product logic, etc.).

## What is deferred to Part 3

- Graded proofs and asymptotic proof (convergence to credence 1)
- Building mathematics on Cred (graded foundations)
- Self-hosting, metareasoning, and self-reference beyond fixed points
- Undecidability and incompleteness considerations
