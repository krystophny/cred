# Open Questions

## Foundational Questions

### Q1: Is Cred Consistent?
Can we derive cred(⊥) > 0 from the axioms?

Note: "Consistency" in Cred means cred(⊥) = 0, not just "no contradiction."

If Cred is inconsistent, cred(⊥) = ε > 0 for some ε, but the system doesn't explode (no ex falso). So inconsistency is bounded, not catastrophic.

### Q2: What's the Relationship to ZFC?
- Can ZFC be interpreted in Cred?
- Can Cred be interpreted in ZFC?
- Are they equiconsistent?

### Q3: Does Cred Have a Model?
Is there a mathematical structure satisfying all Cred axioms?

Candidate: [0,1] with product, complement, standard order, and conditioning via chain rule.

### Q4: Is the Chain Rule Constraint Complete?
Does the chain rule equation/constraint capture everything we want from conditioning?

Might need additional axioms:
- (A | A) = 1? (when A > 0)
- (A | B ∧ C) = ((A | C) | B)? (nested conditioning)

## Logical Questions

### Q5: What's the Proof Theory?
- What's a sequent calculus for Cred?
- Cut elimination?
- Normal forms?

### Q6: What's the Model Theory?
- What are Cred models?
- Completeness theorem?
- Compactness?

### Q7: What's the Computational Complexity?
- Validity in Cred: decidable? What complexity class?
- Satisfiability: decidable?
- Computing credences: computable?

### Q8: Relationship to Relevant Logic
- Is Boolean Cred exactly a known relevant logic (R, E, RM)?
- Or is it a new system?
- What are the exact differences?

## Mathematical Questions

### Q9: Can All of Mathematics Be Done in Cred?
- Arithmetic: Yes (cred 1 statements)
- Analysis: Yes (limits work)
- Set theory: Graded predicates instead of sets
- Category theory: Should work

What, if anything, is lost?

### Q10: Are There New Theorems?
Statements provable in Cred but not classically?

Candidate: Statements about undecidability
```
"G has credence 0.5"  — provable in Cred, not expressible classically
```

### Q11: How Do Forcing and Large Cardinals Work?
- Forcing changes Boolean models of ZFC
- What does forcing do to credence models?
- Do large cardinal axioms affect credences?

## Philosophical Questions

### Q12: What Is Truth in Cred?
- Is cred = 1 "truth"?
- Is cred > 0.5 "more true than false"?
- Is there Platonic truth underlying credence?

### Q13: Is Cred Objective or Subjective?
- De Finetti: Probability is subjective (betting rates)
- Classical logic: Truth is objective
- Cred: ???

Possible answer: Cred is intersubjective — rational agents converge.

### Q14: Does Cred Solve the Liar Paradox?
- Liar has cred = 0.5 — is this a solution or just a different problem?
- Is cred = 0.5 meaningful or just a way to avoid the question?

## Technical Questions

### Q15: How to Handle Higher-Order Quantification?
- First-order: inf/sup over domain
- Second-order: inf/sup over predicates
- Does this work for all predicates or just measurable ones?

### Q16: What About Probability Measures?
- Cred uses product (like probability)
- But no marginalization (no general +)
- Can we recover full probability theory?

### Q17: Can Cred Be Implemented?
- Type checker for Cred?
- Proof assistant?
- What would it look like?

## Connections to Other Fields

### Q18: Quantum Logic?
- Quantum logic rejects distributivity
- Cred rejects ex falso
- Any connection?

### Q19: Paraconsistent Mathematics?
- Brady, Weber: mathematics on relevant/paraconsistent logic
- How does Cred relate?
- Same or different?

### Q20: Machine Learning?
- ML deals with uncertainty, credences
- Can Cred formalize ML reasoning?
- Bayesian inference in Cred?

## Priority Questions

Most important for developing Cred:

1. **Consistency** (Q1): Is the foundation sound?
2. **Model** (Q3): Does a concrete model exist?
3. **Completeness** (Q6): Can we prove completeness?
4. **Implementation** (Q17): Can we build a proof assistant?
5. **Relationship to relevant logic** (Q8): What's the exact connection?

## Research Directions

### Direction 1: Formalization
Build a formal system (syntax, semantics, proof theory).

### Direction 2: Metatheory
Prove consistency, completeness, decidability results.

### Direction 3: Applications
Apply Cred to specific mathematical domains.

### Direction 4: Implementation
Build tools for reasoning in Cred.

### Direction 5: Comparison
Rigorous comparison with fuzzy logic, relevant logic, probability theory.
