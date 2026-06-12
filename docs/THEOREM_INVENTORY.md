# Theorem inventory, axiom ledger, and claim traceability

Every load-bearing paper claim traces to a Lean theorem, a standard citation, or
a marked analogy. This table lists the Lean anchor for each, its module, and its
axiom status. The Lean source builds under `lake build` with zero `sorry`.

## Axiom ledger

`Branch/AxiomAudit.lean` prints `#print axioms` for the core theorems at build
time. The result is uniform: every audited theorem depends only on

```
[propext, Classical.choice, Quot.sound]
```

the three standard Lean 4 / Mathlib axioms, with no `sorryAx`. Two exceptions go
the other way, toward less:

- The finite De Morgan model `Cred.Three` proves the value-algebra laws with **no
  axioms at all** (`neg_neg`, `conj_comm`, `conj_assoc`, `conj_hi`, `conj_lo`,
  `neg_le_neg`); `rank_inj` uses `propext` only. See `docs/VALUE_ALGEBRA.md`.
- The real-free checker verdict `checkBool exampleTree = true` holds by `rfl`
  depending on `propext` only.

`Classical.choice` enters through the hosted reals (real arithmetic and
decidability of real equality), not through the logic of Cred.

## Status legend

- **theorem**: a Lean declaration, named in the table.
- **citation**: a standard result, cited, not reformalized.
- **analogy**: a structured analogy, marked as such in the paper.

## Part 1: congruence classification (axis B)

| Claim | Lean name | Module | Status |
|---|---|---|---|
| `0.5` is the unique negation fixed point | `Credence.neg_fixed_point_unique` | `Core/Value.lean` | theorem |
| Any 3-element negation/conjunction quotient is the Kleene lattice | `three_element_quotient_unique` | `Congruence/Unit.lean` | theorem |
| Boundary classes are singletons under `[0,1]`-multiplication | `UnitCongruence.singleton_zero`, `singleton_one` | `Congruence/Unit.lean` | theorem |
| No nontrivial finite quotient under R-multiplication | `RealCongruence.no_nontrivial_finite_quotient` | `Congruence/Real.lean` | theorem |
| Product does not distribute over De Morgan disjunction | `Credence.conj_disj_not_distrib` | `Core/Value.lean` | theorem |
| Kleene partition is a verified congruence | `kleeneCongruence` | `Congruence/Unit.lean` | theorem |

## Part 2: the probability / many-valued bridge (the interface)

| Claim | Lean name | Module | Status |
|---|---|---|---|
| Conditioning on zero is unconstrained (no ex falso) | `Credence.conditioning_zero_any` | `Cond/Admissible.lean` | theorem |
| Uniqueness of conditioning under positive evidence | `Credence.conditioning_unique` | `Cond/Admissible.lean` | theorem |
| Admissible set trichotomy (singleton / interval / empty) | `cond_singleton_of_pos`, `cond_zero_zero_univ`, `cond_nonempty_iff` | `Cond/Admissible.lean` | theorem |
| LP consequence = positivity on `[0,1]` | `lp_formula_bridge` | `Bridge/LPK3.lean` | theorem |
| K3 consequence = certainty on `[0,1]` | `k3_formula_bridge` | `Bridge/LPK3.lean` | theorem |
| No truth-functional conditional bridge | `no_truthfunctional_cond_bridge` | `Bridge/CondBridge.lean` | theorem |
| Bridge holds at boundaries, fails interior | `cond_bridge_boundary`, `cond_bridge_fails_interior` | `Bridge/CondBridge.lean` | theorem |
| Bayesian update inherits the bridge | `update_bridge` | `Bridge/CondBridge.lean` | theorem |
| Zero-evidence triple | `zero_evidence_duality` | `Bridge/CondBridge.lean` | theorem |
| Min-copula uniqueness on Bayes consistency | `Cond/Copula.lean` results | `Cond/Copula.lean` | theorem |

## Part 3: paradox without explosion, and the arithmetic layer

| Claim | Lean name | Module | Status |
|---|---|---|---|
| Classical evaluation embeds into Cred | `crisp_eval_eq`, `crisp_embedding` | `Bridge/Crisp.lean` | theorem |
| Liar / Russell paradoxes become solution sets | `russell_fixed_point`, `solutions_neg_eq_singleton` | `Predicate.lean`, `Fixpoint.lean` | theorem |
| Curry block: MP + CP + contraction have no common carrier | `curry_block` | `Bridge/Curry.lean` | theorem |
| Sharp no-explosion threshold | `threshold_explosion_countermodel_iff` | `Threshold.lean` | theorem |
| Labelled calculus sound and non-explosive | `derivation_sound`, `labelled_no_ex_falso` | `Sequent.lean` | theorem |
| Proof certificates erase to sound derivations | `Kernel.Proof.sound`, `Kernel.no_ex_falso_certificate` | `Kernel.lean` | theorem |
| Standard model of Q; `N \models Q`; `Con(Q)` | `arithQ.natModel`, `axioms_eval_one`, `arithQ_con` | `Foundation/Arithmetic.lean` | theorem |
| Definable order is Nat order in the standard model | `arithQ.leF_eval_one_iff` | `Foundation/SigmaOne.lean` | theorem |
| Quantifier-free formulas evaluate crisply | `arithQ.quantifierFree_crisp` | `Foundation/SigmaOne.lean` | theorem |
| Sigma-1 completeness (witness extraction) | `arithQ.sigmaOne_witness_complete` | `Foundation/SigmaOne.lean` | theorem |
| Recursion-theoretic representability of provability | `provability_representable`, `Structure.checkCodeNat` | `Foundation/Representability.lean`, `Foundation/CodeChecker.lean` | theorem |
| Representability target for an object Prov formula | `arithQ.RepresentsChecker` | `Foundation/SigmaOne.lean` | theorem (target) |
| Second incompleteness does not internalize | `arithQ.no_internal_loeb_arrow` | `Foundation/SigmaOne.lean` | theorem |
| Goedel sentence pinned to one half | `provGodel` results | `Foundation/ProvabilityDeriv.lean` | theorem |
| Pairing / unpairing represented as object formulas | `arithQ.pairGraph_represents`, `unpairGraph_represents` | `Foundation/Pairing.lean` | theorem |
| List coding (nil/cons/head/tail) represented | `arithQ.consGraph_represents`, `isNilGraph_represents` | `Foundation/SeqCoding.lean` | theorem |
| Goedel beta bounded sequence access represented | `arithQ.betaGraph_represents`, `betaNGraph_represents` | `Foundation/Beta.lean` | theorem |
| Recursive predicate = Sigma-1 beta condition | `arithQ.isTree_iff_beta` | `Foundation/TreeRepr.lean` | theorem |
| Explicit Sigma-1 object formula represents a recursive predicate | `arithQ.treeFormula_represents` | `Foundation/TreeRepr.lean` | theorem |

## Part 4: the irreducible commitment

| Claim | Lean name | Module | Status |
|---|---|---|---|
| Cromwell's rule / no-ex-falso tie | `Cromwell.lean` results | `Cromwell.lean` | theorem |
| Credal-set / admissible-set tie | `Lindley.lean` results | `Lindley.lean` | theorem |
| Fixed-model sequential update = batch update | `sequential_eq_batch` | `Coherence.lean` | theorem |
| Munchhausen trilemma / de Bruijn criterion | n/a | n/a | citation / synthesis |

## Part 5: didactic guide and glossary

Part 5 restates Parts 1-4 results for a general reader. Every Lean name it cites
appears in the rows above (for example `solutions_eq_fixedPoints`,
`mem_cond_iff`, `crossing_out_vs_explosion`, `isClopen_iff_isOpen_and_isOpen_compl`).

## Part 6: universal bootstrapping and seeded self-hosting

| Claim | Lean name | Module | Status |
|---|---|---|---|
| No seed, no run | `SeededSystem.no_empty_bootstrap` | `SeededSystem.lean` | theorem |
| Fixed point gives self-hosting | `selfHosts_of_fixed` | `SeededSystem.lean` | theorem |
| Commitment system embeds, both elements self-host | `SeededSystem.lean` embedding | `SeededSystem.lean` | theorem |
| Commitment conservation under relocation | `commitment_conservation`, `run_invariant_under_relocation` | `MetaBootstrap.lean` | theorem |
| Real-free executable checker soundness | `checkBool_true_sound`, `checkCodeNat_sound` | `Foundation/CheckBool.lean`, `Foundation/CodeChecker.lean` | theorem |
| Real-free value-algebra models; choice-free finite fragment | `RatUnit` instance, `Cred.Three` laws | `Algebra/Rational.lean`, `Algebra/Finite.lean` | theorem |
| Compiler / proof-kernel / AI / biology readings | n/a | n/a | analogy |

## Part 7: graded status in ordinary mathematics

| Claim | Lean name | Module | Status |
|---|---|---|---|
| Structure-degree framework | `Approx.StructureDegree`, `ExactPreserves`, `Preserves`, `preserves_comp` | `Approx/Structure.lean` | theorem |
| Deterministic score recipe | `Approx.scoreEps` + bounds | `Approx/Score.lean` | theorem |
| Positivity, simplex, monotonicity, max-principle, circle, invariant | `implicitUpdate_preserves`, `mix_preserves`, `midpointUpdate_preserves`, `avg_preserves`, `rotate_preserves`, `rot90_firstIntegralPreserving` | `Approx/*.lean` | theorem |
| Symplectic, variational, Lie-group, finite-volume, div-free, SSP, compatible, energy, persistence | `symplectic_rotation`, `leapfrog_momentum_conserved`, `groupStep_preserves`, `fvUpdate_conserves`, `shift_preserves`, `uStep_nonneg`, `d1_comp_d0_eq_zero`, `energy_balance_law`, `long_feature_scores_one` | `Approx/*.lean` | theorem |
| Graded topology recovers classical opens | `open_crisp_iff_isOpen`, `crisp_fuzzyOpen_iff` | `Topology/*.lean` | theorem |
| Clopen is a consistent conjunction, not a contradiction | `isClopen_iff_isOpen_and_isOpen_compl`, `singleton_clopen_discrete_not_standard` | `Topology/Clopen.lean` | theorem |
| Arithmetic/analysis at certainty; graded limits = standard | `add_zero_left_certain`, `tlimit_all_iff_tendsto` | `Math/Nat.lean`, `Math/Metric.lean` | theorem |
| Robustness audit (robust / branch-dependent / inadmissible) | `excluded_middle_robust`, `choice_not_robust`, `audit_verdicts_exclusive` | `Math/Robustness.lean` | theorem |
| Full nonlinear symplectic / FEEC / SSP methods | n/a | n/a | citation |

## Reproducing the ledger

```
cd lean
lake build
lake env lean --run Cred/Branch/AxiomAudit.lean   # prints the axiom ledger
rg -n 'sorry|admit' Cred --glob '*.lean'           # expect no tactic sorry/admit
```
