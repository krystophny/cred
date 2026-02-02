# Part 3: New Proof Techniques and Undecidability

Exploring what becomes possible when truth is graded.

## The Opportunity

Classical logic forces binary outcomes:
- Provable or unprovable
- True or false
- Decidable or undecidable

Cred allows a spectrum:
- Credence from 0 to 1
- Asymptotic proofs
- Undecidability as cred = 0.5

What new techniques and insights emerge?

## Files

- `01-asymptotic-proofs.md` - Proofs that approach but never reach certainty
- `02-fixed-points.md` - Self-reference and credence fixed points
- `03-undecidability.md` - Working with undecidable statements
- `04-new-techniques.md` - Proof techniques unique to Cred
- `05-open-questions.md` - What we don't know yet

## Key Ideas

### Asymptotic Truth
```
lim_{n→∞} cred_n(P) = 1
```
Proven "in the limit" but not at any finite stage.

### Fixed Points
```
cred(L) = ~cred(L) = 0.5
```
Self-referential statements find stable credence.

### Graded Undecidability
```
cred(G) = 0.5 (Gödel sentence)
```
Undecidability IS the credence, not a meta-property.

### Robust Reasoning
```
cred(A ∧ ~A) ≤ 0.25
```
Contradictions bounded, don't explode.

## Questions to Explore

1. Can asymptotic proofs count as "real" proofs?
2. What statements have credence exactly 0.5?
3. Can we compute credences? (decidability of credence)
4. What's the complexity of credence reasoning?
5. Are there new theorems provable only in Cred?
