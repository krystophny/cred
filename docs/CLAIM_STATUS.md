# Claim status ledger

Every theorem-level statement in the flagship paper must be one of the categories
below. This ledger keeps the paper from drifting into unsupported claims. See
`THEOREM_INVENTORY.md` for the full claim-to-Lean-name map.

## Categories

- **Lean theorem**: proved in the Lean development, zero `sorry`, audited axioms.
- **Lean example / witness**: a concrete finite or rational instance, proved.
- **paper definition**: a definition or framing, not a theorem.
- **literature-known**: an established result or ingredient, cited, not a Cred claim.
- **Lean theorem**: a stated goal not yet fully proved; named as such.
- **not claimed**: explicitly disclaimed to forestall misreading.

## Core claims

| Claim | Category | Lean anchor | Assumptions |
|---|---|---|---|
| Admissible-set trichotomy of `Cond(j,e)` | Lean theorem | `cond_singleton_of_pos`, `cond_zero_zero_univ`, `cond_nonempty_iff` | values in `[0,1]` |
| No ex falso at zero evidence (`Cond(0,0)=[0,1]`) | Lean theorem | `conditioning_zero_any` | none |
| Kleene collapse homomorphism; LP=positivity, K3=certainty | Lean theorem | `collapse_*`, `lp_formula_bridge`, `k3_formula_bridge` | none |
| Unique three-element quotient (`[0,1]`-mult) | Lean theorem | `three_element_quotient_unique` | complement + product preserved |
| No non-trivial finite quotient (real-mult) | Lean theorem | `RealCongruence.no_nontrivial_finite_quotient` | unrestricted real multiplication |
| No truth-functional conditional bridge | Lean theorem | `no_truthfunctional_cond_bridge` | min-copula conditional, two witnesses |
| Curry block (no total internal arrow with MP+CP+contraction) | Lean theorem | `curry_block` | product carrier |
| Liar/Russell as solution set `{½}`; truth-teller as full interval | Lean theorem | `solutions_neg_eq_singleton`, `solutions_id_eq_univ` | none |
| Classical recovery at certainty on crisp values | Lean theorem | `crisp_certainty_iff_classical` | atoms in `{0,1}` |

## Foundation layer

| Claim | Category | Lean anchor | Assumptions |
|---|---|---|---|
| Dependence contexts and interval-to-fiber image | Lean theorem | `cond_interval_of_pos`, `collapseIntervalToThree` | positive evidence for the interval map |
| Pairwise marginals/joints do not fix the triple joint | Lean example | `triple_joint_not_determined_by_pairwise` | finite world model |
| Generative first-order calculus, sound | Lean theorem | `genDerives_sound` | the rule set as defined |
| Provenance over the foundation language, sound | Lean theorem | `foundation_provenance_sound` | the Foundation proof type |
| Theory-branch local contradiction without explosion | Lean theorem | `theory_branch_no_explosion` | finite witness structure |
| sqrt2 / sqrt3 core contradictions | Lean theorem | `sqrt2_core_contradiction`, `sqrt3_core_contradiction` | `Nat` arithmetic |

## Probability and measure layer

| Claim | Category | Lean anchor | Assumptions |
|---|---|---|---|
| Entailment = conditional probability one under every measure | Lean theorem | `entails_iff_cond_one` | finite valuation space |
| Entailment = domination under every measure | Lean theorem | `entails_iff_dominated` | finite valuation space |
| Measured conditional obeys the chain rule `c·e=j` | Lean theorem | `cond_chain_rule` | positive evidence |
| Imprecise probability: finite credal family, lower/upper probability | Lean theorem | `lowerP`, `upperP` | finite family |
| Fuzzy observables and lower/upper expectations | Lean theorem | `Expectation`, `lowerE`, `upperE` | finite, rational |
| Cox/Jaynes finite representation (additivity implies measure) | Lean theorem (conservative) | `cox_finite_representation` | normalization, nonnegativity, finite additivity; **not** the full Cox functional-equation derivation |

## Architecture and uniqueness tracks

| Claim | Category | Lean anchor | Assumptions |
|---|---|---|---|
| Generic forall-consequence layer (value algebra + designation) | Lean theorem | `Consequence`, `consequence_cut` | abstract value algebra |
| Boolean/Kleene specializations of the forall layer | Lean theorem | `boolean_forall_consequence_is_classical`, `lp_designation_as_positive` | the named carriers |
| Product residuum vs Cred fiber, made explicit | Lean theorem | `residuum_vs_fiber_positive`, `residuum_vs_fiber_zero` | positive evidence; zero-evidence divergence |
| Chain-rule-faithful conditional coincides with the fiber | Lean theorem | `chainRuleFaithful_eq_Cond` | faithfulness as defined |
| Native continuum rigidity / classical recovery | Lean theorem | `nativeCred_crisp_closed`, `nativeCred_unique_three_quotient` | as in the cited results |

## Explicitly not claimed

- Cred is **not** claimed to be the unique many-valued logic, nor "better fuzzy logic".
- Cred is **not** claimed to subsume probability, imprecise probability, or fuzzy logic.
- The full Cox/Jaynes functional-equation uniqueness is **not** claimed; only the
  conservative finite additivity-implies-measure representation.
- Continuum / measure-theoretic probability is **not** formalized; only finite measures.
- Proof provenance and `T+R` branch semantics are toy/first-cut, **not** a full
  dependency DAG or theory-extension semantics.

Status note: the flagship-epic tracks (#648, #649, #651, #652, #653, #654, #655,
#656, #657) integrated green, so their entries are Lean theorems above;
`THEOREM_INVENTORY.md` carries the full anchor list.
