# Cred Lean Formalization

Machine-verified proofs for the Cred credence algebra. This Lean library is the authoritative source for Part 1: the paper (`part1/paper.tex`) should match the definitions and theorem statements here.

Project goal (beyond Part 1): use this algebra as a foundation for graded mathematics and new proof techniques where propositions and proofs can take values in `[0,1]`.

## Building

```bash
lake build
```

## Structure

- `Cred/Core/Value.lean` - credence values: negation, conjunction, disjunction, order, fixed points, spread
- `Cred/Core/Consequence.lean` - designation, graded consequence, Formula, structural rules, no-explosion
- `Cred/Cond/Admissible.lean` - chain-rule conditioning, admissible sets, Fréchet bounds, path dependence
- `Cred/Cond/Copula.lean` - Bayes consistency on [0,1], min-copula uniqueness, world partitioning
- `Cred/Collapse/ThreeVal.lean` - three-valued credences, RM3/Gödel/product-residuated implications
- `Cred/Collapse/Hom.lean` - collapse homomorphism, impossibility results, Boolean subalgebra
- `Cred/Congruence/Unit.lean` - UnitCongruence classification, Kleene witness
- `Cred/Congruence/Real.lean` - RealCongruence, no non-trivial finite quotient
- `Cred/Bridge/LPK3.lean` - collapse-eval commutativity, LP/K3 bridge theorems
- `Cred/Bridge/CondBridge.lean` - conditional bridge: impossibility, boundary, update bridge
- `Cred/Bridge/Crisp.lean` - classical crisp embedding and conditioning divergence
- `Cred/Bridge/Curry.lean` - product residuation, contraction failure, Curry block
- `Cred/Valuation.lean` - valuations and collapse composition
- `Cred/Update.lean` - Bayesian and Jeffrey conditionalization
- `Cred/Predicate.lean` - graded predicates, quantifiers, Russell fixed point
- `Cred/Fixpoint.lean` - solution sets for liar, truth-teller, Russell, Curry
- `Cred/Threshold.lean` - threshold consequence and sharp bounds
- `Cred/Sequent.lean` - labelled external-conditioning calculus and soundness
- `Cred/Kernel.lean` - type-level proof certificates and sound erasure
- `Cred/Foundation/Language.lean` - first-order language for the foundation layer
- `Cred/Foundation/Semantics.lean` - structures and credence-valued formula evaluation
- `Cred/Foundation/Laws.lean` - crisp equality and quantifier law interfaces
- `Cred/Foundation/Consequence.lean` - semantic consequence for foundation formulas
- `Cred/Foundation/Proof.lean` - first sound threshold calculus for foundation formulas
- `Cred/Foundation/Kernel.lean` - type-level certificates for foundation proof layers
- `Cred/Foundation/Equality.lean` - crisp-equality consequence and proof facts
- `Cred/Foundation/Quantifier.lean` - semantic and proof-theoretic quantifier facts
- `Cred/Foundation/Calculus.lean` - combined foundation consequence and derivation soundness
- `Cred/Foundation/Examples.lean` - exercised foundation proof certificates
- `Cred/Foundation/RuleCode.lean` - trusted rule-code inventory for external checkers
- `Cred/Foundation/Checker.lean` - one-step checked rule application

## Key Theorems

| Theorem | Description |
|---------|-------------|
| `neg_neg` | Negation is involutive |
| `conditioning_zero_any` | Conditioning on 0 is unconstrained (no ex falso) |
| `conditioning_unique` | Conditioning is unique when evidence > 0 |
| `liar_fixed_point` | 0.5 is a negation fixed point |
| `neg_fixed_point_unique` | 0.5 is the unique negation fixed point |
| `conj_disj_not_distrib` | Conjunction does not distribute over disjunction |
| `crisp_embedding` | Classical evaluation embeds into the crisp fragment |
| `curry_block` | MP, conditional proof, and contraction have no common total carrier |
| `russell_fixed_point` | Russell's scalar equation has value 1/2 |
| `derivation_sound` | Labelled derivations are sound for their labels |
| `labelled_no_ex_falso` | A and ~A do not derive an unrelated positive conclusion |
| `Kernel.Proof.sound` | Proof certificates inherit labelled soundness |
| `Kernel.no_ex_falso_certificate` | No certificate derives an unrelated positive conclusion from A and ~A |
| `Foundation.Term.rename`, `Foundation.Term.subst` | Term-level renaming and substitution |
| `Foundation.Term.decEq`, `Foundation.Formula.instDecidableEq` | Decidable syntax equality for certificate checking |
| `Foundation.Term.instSubst`, `Foundation.Formula.instantiate` | Single-variable formula instantiation |
| `Foundation.Formula.rename`, `Foundation.Formula.subst` | Binder-aware formula renaming and substitution |
| `Foundation.Formula.hasEquality` | Structural marker for equality in foundation formulas |
| `Foundation.Formula.hasQuantifier` | Structural marker for quantifiers in foundation formulas |
| `Foundation.Structure.evalFormula` | Credence-valued semantics for foundation formulas |
| `Foundation.Structure.CrispEquality` | Interface for crisp equality laws |
| `Foundation.Structure.QuantifierLaws` | Interface for quantifier introduction and elimination bounds |
| `Foundation.Structure.ThresholdConsequence` | Threshold consequence over all foundation structures |
| `Foundation.Structure.evalTerm_rename`, `evalTerm_subst` | Term evaluation commutes with renaming and substitution |
| `Foundation.Structure.evalFormula_rename`, `evalFormula_subst` | Formula evaluation commutes with renaming and substitution |
| `Foundation.Structure.evalFormula_instantiate` | Formula instantiation updates the bound-variable environment |
| `Foundation.Structure.derivation_sound` | Soundness for the first foundation proof calculus |
| `Foundation.Structure.Proof.sound` | Soundness for first-order proof certificates |
| `Foundation.Structure.CrispProof.sound` | Soundness for crisp-equality proof certificates |
| `Foundation.Structure.CrispProof.equalitySymm`, `equalityTrans` | Equality rules for crisp-equality proof certificates |
| `Foundation.Structure.CrispProof.equalitySubst` | Equality substitution for crisp-equality proof certificates |
| `Foundation.Structure.QuantifierProof.sound` | Soundness for quantifier proof certificates |
| `Foundation.Structure.FoundationProof.sound` | Soundness for combined foundation proof certificates |
| `Foundation.Structure.FoundationProof.weaken`, `cut` | Structural rules for combined foundation proof certificates |
| `Foundation.Structure.FoundationProof.conjElimLeft`, `conjElimRight` | Conjunction elimination for combined foundation proof certificates |
| `Foundation.Structure.FoundationProof.disjIntroLeft`, `disjIntroRight` | Disjunction introduction for combined foundation proof certificates |
| `Foundation.Structure.FoundationProof.equalitySymm`, `equalityTrans` | Equality rules for combined foundation proof certificates |
| `Foundation.Structure.FoundationProof.equalitySubst` | Equality substitution for combined foundation proof certificates |
| `Foundation.Structure.equality_reflexivity_threshold` | Equality reflexivity under crisp-equality laws |
| `Foundation.Structure.equality_symmetry_threshold`, `equality_transitivity_threshold` | Equality symmetry and transitivity under crisp-equality laws |
| `Foundation.Structure.equality_substitution_threshold` | Equality substitution for instantiated formulas under crisp-equality laws |
| `Foundation.Structure.CrispDerivation.equalitySymm`, `equalityTrans` | Crisp-equality proof rules for symmetry and transitivity |
| `Foundation.Structure.CrispDerivation.equalitySubst` | Crisp-equality proof rule for substitution into instantiated formulas |
| `Foundation.Structure.crisp_derivation_sound` | Soundness for the crisp-equality proof layer |
| `Foundation.Structure.forall_elim_semantic`, `exists_intro_semantic` | Semantic quantifier bounds |
| `Foundation.Structure.forall_elim_formula`, `exists_intro_formula` | Formula-level quantifier consequences |
| `Foundation.Structure.quantifier_derivation_sound` | Soundness for the quantifier proof layer |
| `Foundation.Structure.FoundationThresholdConsequence` | Consequence under crisp equality and quantifier laws |
| `Foundation.Structure.FoundationDerivation.weaken`, `cut` | Structural rules for the combined foundation derivation layer |
| `Foundation.Structure.FoundationDerivation.conjElimLeft`, `conjElimRight` | Conjunction elimination for the combined foundation derivation layer |
| `Foundation.Structure.FoundationDerivation.disjIntroLeft`, `disjIntroRight` | Disjunction introduction for the combined foundation derivation layer |
| `Foundation.Structure.FoundationDerivation.equalitySymm`, `equalityTrans` | Equality proof rules for the combined foundation derivation layer |
| `Foundation.Structure.FoundationDerivation.equalitySubst` | Equality substitution for the combined foundation derivation layer |
| `Foundation.Structure.foundation_derivation_sound` | Soundness for the combined foundation derivation layer |
| `Foundation.Structure.equalitySymmetryCertificate`, `equalitySubstitutionCertificate` | Example foundation equality certificates |
| `Foundation.Structure.forallElimCertificate`, `existsIntroCertificate` | Example foundation quantifier certificates |
| `Foundation.Structure.forallElimCertificateTree_checks`, `equalitySubstitutionCertificateTree_checks` | Recursive checker examples that accept certificate trees |
| `Foundation.Structure.forallElimCertificateTree_checks_to`, `equalitySubstitutionCertificateTree_checks_to` | Recursive checker examples with exact checked outputs |
| `Foundation.Structure.forallElimCertificateTree_sound`, `equalitySubstitutionCertificateTree_sound` | Checked certificate tree examples yield sound foundation consequences |
| `Foundation.Structure.forallElimCertificateTree_shapeOK`, `equalitySubstitutionCertificateTree_shapeOK` | Structural certificate precheck examples that accept well-formed trees |
| `Foundation.Structure.forallElimCertificateTree_header_shapeOK`, `equalitySubstitutionCertificateTree_header_shapeOK` | Header examples that accept well-formed roots |
| `Foundation.Structure.forallElimCertificateTree_headersShapeOK`, `equalitySubstitutionCertificateTree_headersShapeOK` | Recursive header examples that accept well-formed trees |
| `Foundation.Structure.forallElimCertificateTree_missing_child_fails`, `equalitySubstitutionCertificateTree_missing_child_fails` | Recursive checker examples that reject certificate trees with missing children |
| `Foundation.Structure.forallElimCertificateTree_missing_child_shape_fails`, `equalitySubstitutionCertificateTree_missing_child_shape_fails` | Structural certificate precheck examples that reject missing children |
| `Foundation.Structure.forallElimCertificateTree_missing_child_header_fails`, `equalitySubstitutionCertificateTree_missing_child_header_fails`, `unknownFoundationCertificateHeader_fails` | Header examples that reject bad arity or unknown rule names |
| `Foundation.Structure.forallElimCertificateTree_missing_child_headers_fail`, `equalitySubstitutionCertificateTree_missing_child_headers_fail` | Recursive header examples that reject malformed trees |
| `Foundation.Structure.FoundationRuleCode` | Trusted rule names for the foundation certificate checker boundary |
| `Foundation.Structure.FoundationRuleCode.ofName_name` | Rule-code string names parse back to their source code |
| `Foundation.Structure.FoundationRuleCode.childCount` | Trusted rule codes state the required number of checked children |
| `Foundation.Structure.mem_trustedFoundationRules` | Every trusted foundation rule code is listed |
| `Foundation.Structure.FoundationRulePayload.childCount_eq_code` | Rule payloads use the child count of their trusted code |
| `Foundation.Structure.FoundationRulePayload.header_shapeOK` | Typed rule payloads produce accepted serialized headers |
| `Foundation.Structure.FoundationCertificateHeader.matchesPayload_payload_header` | Canonical payload headers match their typed payloads |
| `Foundation.Structure.applyFoundationRule_some_childCount` | Successful rule application has the arity declared by its rule code |
| `Foundation.Structure.applyFoundationRule` | One-step checker from rule payloads and checked children to typed certificates |
| `Foundation.Structure.FoundationCertificateHeader.shapeOK` | Serialized certificate headers parse rule names and check arity |
| `Foundation.Structure.FoundationCertificateHeader.shapeOK_false_of_ruleCode?_none` | Unknown rule names fail the header check |
| `Foundation.Structure.FoundationCertificateTree.header_shapeOK_true_iff` | Tree headers pass exactly when root arity matches |
| `Foundation.Structure.FoundationCertificateTree.headersShapeOK_eq_shapeOK` | Recursive header precheck agrees with structural precheck |
| `Foundation.Structure.FoundationCertificateTree.ruleName_roundtrip` | Certificate tree rule names parse back to their rule codes |
| `Foundation.Structure.CheckedFoundationProof.sound` | Checked proof objects produce foundation consequences |
| `Foundation.Structure.FoundationCertificateTree.shapeOK_true_arityMatches` | Structural precheck success implies root arity matches |
| `Foundation.Structure.FoundationCertificateTree.shapeOK_true_allAritiesMatch` | Structural precheck success implies every node has matching arity |
| `Foundation.Structure.checkFoundationCertificate_some_arityMatches` | Successful certificate checks have matching root arity |
| `Foundation.Structure.checkFoundationCertificate_some_allAritiesMatch` | Successful certificate checks have matching arity at every node |
| `Foundation.Structure.checkFoundationCertificate_some_shapeOK` | Successful certificate checks imply the structural precheck accepts |
| `Foundation.Structure.checkFoundationCertificate_none_of_shapeOK_false` | Failed structural precheck forces certificate rejection |
| `Foundation.Structure.checkFoundationCertificate_sound` | Successful certificate checks produce sound foundation consequences |
| `Foundation.Structure.checkFoundationCertificate` | Recursive checker from certificate trees to typed certificates |
| `Foundation.Structure.FoundationCertificateEnvelope.localShapeOK` | External envelope headers must match their typed payload and child count |
| `Foundation.Structure.checkFoundationCertificateEnvelope_some_matchesPayload` | Successful envelope checks imply the supplied header matches the payload |
| `Foundation.Structure.checkFoundationCertificateEnvelope_sound` | Successful envelope checks produce sound foundation consequences |
| `Foundation.Structure.forallElimEnvelope_localShapeOK` | A well-formed external envelope passes the local header check |
| `Foundation.Structure.forallElimEnvelope_bad_header_fails` | A forged root header is rejected before certificate acceptance |
| `Foundation.Structure.SerializedFoundationHeader.decode` | Raw header input decodes only after rule-name and arity checks |
| `Foundation.Structure.SerializedFoundationHeader.decode_none_of_unknown` | Unknown serialized rule names fail before trusted headers are built |
| `Foundation.Structure.SerializedFoundationHeader.decode_none_of_bad_childCount` | Wrong serialized arities fail before trusted headers are built |
| `Foundation.Structure.serialized_bad_arity_header_fails` | Concrete bad-arity header example is rejected |

## Dependencies

- Lean 4 (see lean-toolchain)
- Mathlib 4.16.0
