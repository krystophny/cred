# CLAUDE.md

## Current Focus: Papers and formalization publication-ready

Part 1: congruence classification of the product De Morgan triplet (6 sections + conclusion + 2 appendices, 12 pages).
Part 2: self-contained paper on chain-rule conditioning as a bridge between probability and many-valued logic (8 sections + 2 appendices, 24 pages).
Part 3: paradox without explosion: crisp fragments, solution sets, graded comprehension, and external conditioning.
All Lean proofs fully verified, zero sorry. All papers build clean.

## Build

```bash
cd lean && lake build              # Lean formalization
cd part1 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
cd part2 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
cd part3 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

Toolchain: Lean `v4.16.0` + mathlib `v4.16.0`. Correctness = `lake build` succeeds and theorems type-check.

## Primitives

```
[0,1]   credence values
0       impossibility
1       certainty
~c      negation (1 - c)
c₁⊗c₂   conjunction (product)
c₁⊔c₂   disjunction (De Morgan dual)
(A|B)   conditioning (primitive; chain rule)
```

**Chain rule (primitive conditioning):** `cred(A|B) ⊗ cred(B) = cred(A ∧ B)`

When `cred(B) = 0`: the equation imposes no constraint on `cred(A|B)` (any value works). There is intentionally **no ex falso** / explosion from impossible evidence.

Keep the separation clear: `⊗`/`⊔` are the core algebraic operations (product / De Morgan dual). Dependence is handled by supplying an explicit joint credence in `Cred.Credence.Conditioning` rather than treating `⊗` as a general rule for `cred(A ∧ B)`.

## Repo Map

- `lean/Cred/Core/Value.lean`: credence values: negation, product conjunction, disjunction, order, fixed points, spread, equilibria.
- `lean/Cred/Core/Consequence.lean`: K3/LP designation, graded consequence, Formula, eval, structural rules, no-explosion theorems.
- `lean/Cred/Cond/Admissible.lean`: chain-rule conditioning, admissible sets (Cond), Fréchet bounds, conditioning tables, path dependence.
- `lean/Cred/Cond/Copula.lean`: Bayes consistency on [0,1], min-copula uniqueness, world partitioning.
- `lean/Cred/Collapse/ThreeVal.lean`: three-valued credences, RM3/Gödel/product-residuated implications.
- `lean/Cred/Collapse/Hom.lean`: collapse homomorphism, no-Gödel/no-Łukasiewicz collapse, Boolean subalgebra.
- `lean/Cred/Congruence/Unit.lean`: UnitCongruence classification, Kleene witness, three-element quotient uniqueness.
- `lean/Cred/Congruence/Real.lean`: RealCongruence, scaling trick, no non-trivial finite quotient.
- `lean/Cred/Bridge/LPK3.lean`: collapse-eval commutativity, LP/K3 bridge theorems.
- `lean/Cred/Bridge/CondBridge.lean`: conditional bridge: impossibility, boundary, update bridge, zero-evidence triple.
- `lean/Cred/Bridge/Crisp.lean`: Boolean embedding, crisp consequence coincidence, conditioning divergence.
- `lean/Cred/Bridge/Curry.lean`: product residuation, contraction failure, Curry block.
- `lean/Cred/Valuation.lean`: valuations (CpValuation, IndepValuation, JointValuation).
- `lean/Cred/Update.lean`: Bayesian and Jeffrey conditionalization.
- `lean/Cred/Predicate.lean`: graded predicates, quantifiers, Russell fixed point.
- `lean/Cred/Fixpoint.lean`: solution sets for liar, truth-teller, Curry, and zero-evidence conditioning.
- `lean/Cred/Threshold.lean`: threshold consequence, structural rules, sharp explosion and excluded-middle bounds.
- `lean/Cred/Sequent.lean`: labelled external-conditioning calculus, soundness, chain-rule cut, no-ex-falso witness.
- `lean/Cred/Kernel.lean`: type-level proof certificates, erasure to labelled derivations, certificate soundness.
- `lean/Cred/Foundation/Language.lean`: first-order terms, equality, predicates, quantifiers, and no internal conditional.
- `lean/Cred/Foundation/Semantics.lean`: structures, assignments, term evaluation, formula evaluation into credences.
- `lean/Cred/Foundation/Laws.lean`: crisp equality and quantifier law interfaces.
- `lean/Cred/Foundation/Consequence.lean`: threshold and certainty consequence for foundation formulas.
- `lean/Cred/Foundation/Proof.lean`: first threshold proof calculus for foundation formulas, with soundness.
- `lean/Cred/Foundation/Kernel.lean`: type-level certificates for foundation derivations, law-specific derivations, erasure, and soundness.
- `lean/Cred/Foundation/Equality.lean`: crisp-equality consequence target, equality reflexivity, and sound crisp derivations.
- `lean/Cred/Foundation/Quantifier.lean`: quantifier-law consequence target, formula instantiation rules, and sound quantifier derivations.
- `lean/Cred/Foundation/Calculus.lean`: combined foundation consequence with equality and quantifier laws.
- `lean/Cred/Foundation/Examples.lean`: small foundation proof certificates and their soundness facts.
- `lean/Cred/Foundation/RuleCode.lean`: trusted rule-code inventory for future external checking.
- `lean/Cred/Foundation/Checker.lean`: one-step rule checker returning typed foundation certificates.
- `part1/paper.tex`: congruence classification (6 sections + conclusion + 2 appendices, 12 pages).
- `part2/paper.tex`: bridge paper (8 sections + 2 appendices, 24 pages; self-contained).
- `part3/paper.tex`: foundations paper: paradox without explosion, crisp fragments, solution sets, and external conditioning.

## Key Results to Keep Green (Lean)

Core:
- `Cred.Credence.conditioning_zero_any` (conditioning on 0 is unconstrained)
- `Cred.Credence.conditioning_unique` (uniqueness when evidence has positive credence)
- `Cred.Credence.liar_fixed_point`, `Cred.Credence.neg_fixed_point_unique` (0.5 fixed point and uniqueness)
- `Cred.Credence.conj_disj_not_distrib` (⊗ does not distribute over ⊔)

Admissible-set conditioning (Cond/Admissible.lean, Bridge/CondBridge.lean):
- `Cred.Credence.Cond` (admissible set {c | c ⊗ e = j} as named primitive)
- `cond_singleton_of_pos`, `cond_zero_zero_univ`, `cond_nonempty_iff` (trichotomy: singleton / full interval / empty)
- `mem_cond_iff` (membership = Conditioning witness)
- `zero_evidence_duality_cond`, `cond_interior_range` (CondBridge restatements through Cond)

Collapse / congruence:
- `Cred.ThreeVal.rm3_ex_falso` (RM3 implication has explosion row)
- `Cred.ThreeVal.cred_no_ex_falso` (Cred blocks ex falso via unconstrained conditioning)
- `three_element_quotient_unique`, `zero_equiv_forces_trivial`, `no_boolean_neg_retraction`
- `Cred.UnitCongruence.singleton_zero`, `singleton_one` (boundary singletons under [0,1]-mult)
- `Cred.RealCongruence.no_nontrivial_finite_quotient` (scaling trick, no finite quotient under R-mult)
- `Cred.kleeneCongruence` (Kleene partition as verified UnitCongruence)

Bridge (from Bridge/LPK3.lean and Core/Consequence.lean):
- `lp_formula_bridge`, `k3_formula_bridge` (LP = positivity, K3 = certainty consequence)
- `k3_no_tautology`, `lp_no_explosion`, `graded_no_explosion`

Conditional bridge (from Bridge/CondBridge.lean):
- `no_truthfunctional_cond_bridge` (impossibility: no truth-functional conditional bridge)
- `cond_bridge_boundary` (bridge holds at boundaries)
- `cond_bridge_fails_interior` (bridge fails for interior pairs)
- `update_bridge` (Bayesian update inherits the bridge)
- `zero_evidence_duality` (zero-evidence triple)

Crisp bridge (from Bridge/Crisp.lean):
- `crisp_eval_eq`, `crisp_embedding` (classical evaluation embeds into Cred)
- `crisp_certainty_iff_classical`, `crisp_positivity_iff_classical`
- `material_divergence`, `cond_underdetermined_iff` (exact divergence from material implication)

Curry bridge (from Bridge/Curry.lean):
- `residuation_unique`, `prodResid_unique_positive` (MP + CP pin the product residuum)
- `prod_resid_no_contraction`, `curry_block` (contraction is incompatible)
- `curry_fixed_point_positive`, `curry_no_fixed_point_zero` (Curry equations at the boundary)

Predicates (from Predicate.lean):
- `quantifier_duality_val`, `russell_fixed_point`, `crisp_inf_zero_iff`

Fixpoints (from Fixpoint.lean):
- `solutions`, `solutions_neg_eq_singleton`, `solutions_id_eq_univ`
- `truth_teller_same_shape_as_zero_evidence`
- `curry_sqrt_solution`, `curry_zero_solutions_empty`

Thresholds (from Threshold.lean):
- `thresholdConsequence`, `threshold_reflexivity`, `threshold_monotonicity`, `threshold_cut`
- `threshold_one_iff_certainty`, `formulaPositivity_iff_exists_threshold`
- `threshold_explosion_countermodel_iff`, `threshold_excluded_middle_iff`

Sequents (from Sequent.lean):
- `Derivation` (labelled derivations with positive, certain, and threshold labels)
- `CondJudgment` (external conditioning side judgments; no Formula arrow constructor)
- `derivation_sound`, `derivation_sound_thresholdConsequence`
- `derivation_sound_formulaCertainty`, `derivation_sound_formulaPositivity`
- `labelled_no_ex_falso` (A and ~A do not derive an unrelated positive conclusion)

Kernel certificates (from Kernel.lean):
- `Kernel.Proof` (type-level proof certificates for labelled derivations)
- `Kernel.Proof.toDerivation`, `Kernel.Proof.sound`
- `Kernel.Proof.to_thresholdConsequence`, `to_formulaCertainty`, `to_formulaPositivity`
- `Kernel.no_ex_falso_certificate` (no certificate derives unrelated positive conclusions from A and ~A)

Foundation language (from Foundation/Language.lean):
- `Foundation.Term`, `Foundation.Formula`
- `Term.decEq`, formula `DecidableEq`
- `Term.rename`, `Term.subst`
- `Term.upRenaming`, `Term.liftSubst`, `Term.instSubst`
- `Formula.rename`, `Formula.subst`, `Formula.instantiate`
- Formula constructors include equality and quantifiers; there is no implication or conditional constructor
- `Formula.hasEquality`, `Formula.hasQuantifier`

Foundation semantics (from Foundation/Semantics.lean):
- `Foundation.Structure` (domain, functions, predicates, equality, quantifier operations)
- `Structure.evalTerm`, `Structure.evalTermList`, `Structure.evalFormula`
- `evalTerm_rename`, `evalTerm_subst`
- `evalFormula_rename`, `evalFormula_subst`
- `evalFormula_instantiate`
- Equality and quantifier laws are deliberately separate from the raw semantic interface

Foundation laws (from Foundation/Laws.lean):
- `Structure.CrispEquality`, `Structure.QuantifierLaws`
- `equality_no_false_positive`, `equality_reflexive_one`
- `forall_instantiates`, `exists_introduces`

Foundation consequence (from Foundation/Consequence.lean):
- `Structure.ThresholdConsequence`, `Structure.CertaintyConsequence`
- `threshold_reflexivity`, `threshold_monotonicity`, `threshold_cut`
- `certainty_reflexivity`

Foundation proof (from Foundation/Proof.lean):
- `Structure.Derivation`
- `derivation_sound`
- Rules cover hypotheses, weakening, cut, conjunction elimination, and disjunction introduction

Foundation kernel (from Foundation/Kernel.lean):
- `Structure.Proof`
- `Proof.toDerivation`, `Proof.sound`
- `Structure.CrispProof`
- `CrispProof.equalitySymm`, `CrispProof.equalityTrans`
- `CrispProof.equalitySubst`
- `CrispProof.toDerivation`, `CrispProof.sound`
- `Structure.QuantifierProof`
- `QuantifierProof.toDerivation`, `QuantifierProof.sound`
- `Structure.FoundationProof`
- `FoundationProof.weaken`, `FoundationProof.cut`
- `FoundationProof.conjElimLeft`, `FoundationProof.conjElimRight`
- `FoundationProof.disjIntroLeft`, `FoundationProof.disjIntroRight`
- `FoundationProof.equalitySymm`, `FoundationProof.equalityTrans`
- `FoundationProof.equalitySubst`
- `FoundationProof.toDerivation`, `FoundationProof.sound`

Foundation equality (from Foundation/Equality.lean):
- `Structure.CrispThresholdConsequence`
- `threshold_to_crisp`
- `equality_reflexivity_threshold`
- `equality_symmetry_threshold`, `equality_transitivity_threshold`
- `equality_substitution_threshold`
- `Structure.CrispDerivation`
- `CrispDerivation.equalitySymm`, `CrispDerivation.equalityTrans`
- `CrispDerivation.equalitySubst`
- `crisp_derivation_sound`

Foundation quantifiers (from Foundation/Quantifier.lean):
- `Structure.QuantifierThresholdConsequence`
- `threshold_to_quantifier`
- `forall_elim_semantic`, `exists_intro_semantic`
- `forall_elim_formula`, `exists_intro_formula`
- `Structure.QuantifierDerivation`
- `quantifier_derivation_sound`

Foundation calculus (from Foundation/Calculus.lean):
- `Structure.FoundationThresholdConsequence`
- `threshold_to_foundation`, `crisp_to_foundation`, `quantifier_to_foundation`
- `Structure.FoundationDerivation`
- `FoundationDerivation.weaken`, `FoundationDerivation.cut`
- `FoundationDerivation.conjElimLeft`, `FoundationDerivation.conjElimRight`
- `FoundationDerivation.disjIntroLeft`, `FoundationDerivation.disjIntroRight`
- `FoundationDerivation.equalitySymm`, `FoundationDerivation.equalityTrans`
- `FoundationDerivation.equalitySubst`
- `foundation_derivation_sound`

Foundation examples (from Foundation/Examples.lean):
- `equalitySymmetryCertificate`, `equalitySubstitutionCertificate`
- `forallElimCertificate`, `existsIntroCertificate`
- `forallElimCertificateTree`, `equalitySubstitutionCertificateTree`
- `forallElimCertificateTree_checks`, `equalitySubstitutionCertificateTree_checks`
- `forallElimCertificateTree_shapeOK`, `equalitySubstitutionCertificateTree_shapeOK`
- `forallElimCertificateTree_missing_child_fails`
- `equalitySubstitutionCertificateTree_missing_child_fails`
- `forallElimCertificateTree_missing_child_shape_fails`
- `equalitySubstitutionCertificateTree_missing_child_shape_fails`
- `equality_symmetry_certificate_sound`, `equality_substitution_certificate_sound`
- `forall_elim_certificate_sound`, `exists_intro_certificate_sound`

Foundation rule codes (from Foundation/RuleCode.lean):
- `Structure.FoundationRuleCode`
- `FoundationRuleCode.name`, `FoundationRuleCode.ofName`
- `FoundationRuleCode.childCount`
- `FoundationRuleCode.ofName_name`, `FoundationRuleCode.ofName_eq_some_mem`
- `trustedFoundationRules`, `mem_trustedFoundationRules`

Foundation checker (from Foundation/Checker.lean):
- `Structure.CheckedFoundationProof`
- `CheckedFoundationProof.sound`
- `Structure.FoundationRulePayload`
- `FoundationRulePayload.code`, `FoundationRulePayload.childCount`
- `applyFoundationRuleUnchecked`
- `applyFoundationRule`
- `applyFoundationRule_some_childCount`
- `Structure.FoundationCertificateTree`
- `FoundationCertificateTree.ruleCode`, `FoundationCertificateTree.ruleName`
- `FoundationCertificateTree.childCount`, `FoundationCertificateTree.children`
- `FoundationCertificateTree.arityMatches`
- `FoundationCertificateTree.allAritiesMatch`
- `FoundationCertificateTree.allAritiesMatchList`
- `FoundationCertificateTree.shapeOK`, `FoundationCertificateTree.shapeOKList`
- `FoundationCertificateTree.shapeOK_true_arityMatches`
- `FoundationCertificateTree.shapeOK_true_allAritiesMatch`
- `FoundationCertificateTree.shapeOKList_true_allAritiesMatchList`
- `FoundationCertificateTree.ruleName_roundtrip`
- `checkFoundationCertificate_some_arityMatches`
- `checkFoundationCertificate_some_allAritiesMatch`
- `checkFoundationCertificateList_some_allAritiesMatchList`
- `checkFoundationCertificate_some_shapeOK`
- `checkFoundationCertificateList_some_shapeOKList`
- `checkFoundationCertificate_none_of_shapeOK_false`
- `checkFoundationCertificateList_none_of_shapeOKList_false`
- `checkFoundationCertificate_sound`
- `checkFoundationCertificate`, `checkFoundationCertificateList`

## Philosophy

**Inference constrains:** evidence narrows possibilities from prior uncertainty; impossible evidence (credence 0) provides no constraint.

**Conditional first:** conditioning is primitive (chain rule), not division; this is the key design choice that avoids explosion at 0.
