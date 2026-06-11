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
- `Cred/Foundation/Kernel.lean` - type-level certificates for foundation and quantifier proofs
- `Cred/Foundation/Equality.lean` - crisp-equality consequence and proof facts
- `Cred/Foundation/Quantifier.lean` - semantic and proof-theoretic quantifier facts
- `Cred/Foundation/Calculus.lean` - combined foundation consequence and derivation soundness

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
| `Foundation.Structure.QuantifierProof.sound` | Soundness for quantifier proof certificates |
| `Foundation.Structure.equality_reflexivity_threshold` | Equality reflexivity under crisp-equality laws |
| `Foundation.Structure.crisp_derivation_sound` | Soundness for the crisp-equality proof layer |
| `Foundation.Structure.forall_elim_semantic`, `exists_intro_semantic` | Semantic quantifier bounds |
| `Foundation.Structure.forall_elim_formula`, `exists_intro_formula` | Formula-level quantifier consequences |
| `Foundation.Structure.quantifier_derivation_sound` | Soundness for the quantifier proof layer |
| `Foundation.Structure.FoundationThresholdConsequence` | Consequence under crisp equality and quantifier laws |
| `Foundation.Structure.foundation_derivation_sound` | Soundness for the combined foundation derivation layer |

## Dependencies

- Lean 4 (see lean-toolchain)
- Mathlib 4.16.0
