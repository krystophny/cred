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
| Truth-functional idempotent scalar joint is forced to min under copula-like assumptions; general probability must supply event-specific joints | `min_copula_unique`, `truth_functional_forces_min`, `truth_functional_idempotent_implies_max_dependence` | `Cond/Copula.lean` | theorem |

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

## Dependence, proof theory, and toy worlds (foundation layer, issue #645)

These anchors are foundation-layer toy and dependence constructions, not
publication-grade results. They back the worked examples and the explicit
joint-credence machinery: dependence handled by supplying a joint context
rather than by overloading `⊗`.

### Dependence (`Cred/Dependence/`)

| Claim | Lean name | Module | Status |
|---|---|---|---|
| Joint context as exact / coherent / interval data; family of joints | `ExactJointContext`, `CoherentJointContext`, `IntervalJointContext`, `JointFamily` | `Dependence/Context.lean` | theorem |
| Conditioning is an interval under positive evidence | `cond_interval_of_pos` | `Dependence/Conditioning.lean` | theorem |
| Conditioning fiber on zero evidence is unconstrained | `cond_fiber_zero` | `Dependence/Conditioning.lean` | theorem |
| Robust above threshold; threshold-sensitive dependence | `robust_above_threshold`, `dependence_sensitive` | `Dependence/Conditioning.lean` | theorem |
| Three-valued collapse of an interval verdict | `collapseIntervalToThree`, `RobustStatus` | `Dependence/RobustCollapse.lean` | theorem |
| Collapse characterizations (incoherent / underdetermined / robust 0,1,half) | `collapse_incoherent_iff`, `collapse_underdetermined_of_full`, `collapse_robustZero_imp`, `collapse_robustOne_iff`, `collapse_robustHalf_imp` | `Dependence/RobustCollapse.lean` | theorem |

### Proof theory (`Cred/ProofTheory/`)

| Claim | Lean name | Module | Status |
|---|---|---|---|
| Labels and their designation of credences | `Label`, `designates` | `ProofTheory/Labels.lean` | theorem |
| Generative derivation relation, sound | `Derives`, `generative_sound` | `ProofTheory/Generative.lean` | theorem |
| Conjunction introduction at threshold `s⊗t`; per-rule soundness | `conjIntro`, `conjIntro_sound`, `conjElimLeft_sound`, `conjElimRight_sound`, `disjIntroLeft_sound`, `disjIntroRight_sound` | `ProofTheory/Generative.lean` | theorem |
| Generative first-order calculus (equality substitution, forall-elim, exists-intro) with soundness | `GenDerives`, `genDerives_sound`, `equalitySubst_sound`, `forallElim_sound`, `existsIntro_sound` | `ProofTheory/GenerativeQuant.lean` | theorem |
| Assumption provenance tracked and sound | `usedAssumptions`, `provenance_sound` | `ProofTheory/Provenance.lean` | theorem |
| Local contradiction does not explode | `local_contradiction_no_explosion` | `ProofTheory/Branches.lean` | theorem |

### Examples (`Cred/Examples/`)

| Claim | Lean name | Module | Status |
|---|---|---|---|
| Finite-world entailment is set inclusion | `entails_iff_subset` | `Examples/FiniteWorlds.lean` | theorem |
| Entailment witnesses: `A` not `B`, `A` entails `C` | `A_not_entails_B`, `A_entails_C` | `Examples/FiniteWorlds.lean` | theorem |
| Pointwise values do not determine entailment; marginals do not determine the joint | `pointwise_does_not_determine`, `joint_not_determined_by_marginals` | `Examples/FiniteWorlds.lean` | theorem |
| Issue-anchor restatements; product/independence witness | `truthSet_subset_iff_entails`, `finite_pointwise_truth_not_connection`, `finite_same_marginals_different_joint`, `finite_independence_example` | `Examples/FiniteWorlds.lean` | theorem |
| Interval collapse worked cases (half / sensitive / underdetermined / incoherent) | `collapse_interval_interior_robust_half`, `collapse_interval_boundary_sensitive`, `zero_evidence_collapse_underdetermined`, `empty_fiber_collapse_incoherent` | `Examples/RobustCollapse.lean` | theorem |
| Elegant elementary results: no-explosion reductio, liar/truth-teller solution sets, total zero-evidence conditioning, independence irrelevance | `contradiction_does_not_force_unrelated_atom`, `liar_solution_set_is_half`, `truth_teller_solution_set_is_univ`, `zero_evidence_conditioning_is_total`, `independent_evidence_conditional_is_prior` | `Examples/Elegant.lean` | theorem |
| Robust conditioning: Frechet bounds, product joint, conditioning interval | `frechet_lower`, `frechet_upper`, `product_joint`, `cond_interval` | `Examples/RobustConditioning.lean` | theorem |
| Robust at low threshold, sensitive at high threshold | `robust_at_low_threshold`, `sensitive_at_high_threshold` | `Examples/RobustConditioning.lean` | theorem |
| Provenance worked cases | `used_assumptions_example`, `entails_but_unused` | `Examples/ProofProvenance.lean` | theorem |
| Local contradiction without explosion, worked | `local_contradiction_no_explosion_example` | `Examples/Branches.lean` | theorem |
| Sqrt-2 core contradiction and dependency chain | `sqrt2_core_contradiction`, `sqrt2_dependency_chain` | `Examples/Sqrt2Branch.lean` | theorem |

### Math (`Cred/Math/`)

| Claim | Lean name | Module | Status |
|---|---|---|---|
| Even square implies even base | `even_square_implies_even` | `Math/Parity.lean` | theorem |
| Sqrt-2 core: both `p` and `q` even, hence not coprime | `sqrt2_core_even_p`, `sqrt2_core_even_q`, `not_coprime_if_both_even` | `Math/Divisibility.lean` | theorem |

## Reproducing the ledger

```
cd lean
lake build
lake env lean --run Cred/Branch/AxiomAudit.lean   # prints the axiom ledger
rg -n 'sorry|admit' Cred --glob '*.lean'           # expect no tactic sorry/admit
```