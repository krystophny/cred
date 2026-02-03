# Working with Undecidable Statements

## Classical Undecidability

A statement P is **undecidable** in system S if:
- S cannot prove P
- S cannot prove NOT P

Examples:
- Continuum Hypothesis (CH) in ZFC
- Halting problem (algorithmically undecidable)

## Cred and Undecidability

Important distinctions:

1. **Self-negating sentences** (liar: L = NOT L) have cred = 0.5 as a fixed point
2. **Independent sentences** (CH in ZFC) have unconstrained credence given the axioms
3. **Godel sentences** have definite truth values in standard models (TRUE for consistent systems)

Cred does NOT automatically assign 0.5 to all "undecidable" statements. The 0.5 fixed point applies only to self-negating sentences.

## Types of 0.5 Credence

Not all cred = 0.5 is the same:

### Unknown (Epistemic)
```
cred(P) = 0.5 because we lack evidence
Evidence could move it toward 0 or 1
```

### Undecidable (Logical)
```
cred(P) = 0.5 because no proof exists either way
Evidence cannot move it (in principle)
```

### Self-Referential (Fixed Point)
```
cred(P) = 0.5 because P = ~P
The value is forced by self-reference
```

## The Halting Problem in Cred

Does program M halt on input x?

```
Halt(M, x) : {0, 1}  — crisp, but uncomputable

cred(Halt(M, x)) = ???
```

For specific M, x:
- If we run M and it halts: cred → 1
- If we run M and it hasn't halted yet: cred = 0.5 (unknown)
- If we prove M loops: cred → 0

The undecidability is: no algorithm computes cred(Halt(M, x)) for all M, x.

But for individual cases, cred can be determined!

## Independence in Cred

CH is independent of ZFC:
```
ZFC ⊬ CH
ZFC ⊬ ~CH
```

In Cred:
```
cred(CH | ZFC) = unconstrained
```

The chain rule: cred(CH | ZFC) * cred(ZFC) = cred(CH ∧ ZFC)

If cred(ZFC) = 1 (we accept ZFC):
```
cred(CH | ZFC) = cred(CH ∧ ZFC)
```

But ZFC doesn't constrain CH, so cred(CH | ZFC) is **genuinely indeterminate**.

This is different from 0.5. It's "not determined by the axioms."

## Working With Independent Statements

### Strategy 1: Recognize Independence
```
cred(CH | ZFC) is unconstrained by ZFC axioms
This is different from self-negation (which forces 0.5)
```

### Strategy 2: Add Axioms
```
cred(CH | ZFC + CH) = 1
cred(CH | ZFC + ~CH) = 0
```

Adding axioms determines previously undetermined credences.

### Strategy 3: Consider Extensions
```
cred(CH | ZFC + large cardinals) might be constrained
Different extensions give different credences
```

### Strategy 4: Meta-Analysis
```
cred(CH is "true" in intended model) ≈ ???
Philosophical/intuitive judgment
```

## The Credence Spectrum

```
Provably true:     cred = 1 (from axioms)
Provably false:    cred = 0 (from axioms)
Independent:       cred unconstrained by axioms
Self-negating:     cred = 0.5 (negation fixed point, e.g., liar)
Unknown:           cred reflects epistemic uncertainty
```

Note: "Self-negating" (X = NOT X) is different from "independent" (axioms don't determine X). The liar is self-negating. CH is independent. Godel sentences are TRUE in standard models but unprovable.

## Practical Implications

### For Mathematics
- Undecidable doesn't mean "unknown" — it means cred = 0.5 exactly
- We can still reason about undecidable statements
- Adding axioms is explicit credence assignment

### For Computer Science
- Halting problem: uncomputable, but cred is well-defined
- Algorithmic: can compute cred for restricted classes
- Approximation: can bound cred with partial evidence

### For Philosophy
- "Is CH true?" becomes "What is cred(CH)?"
- The question has an answer (possibly 0.5 or unconstrained)
- Truth = credence 1, not some Platonic fact

## Computing with Undecidable Credences

Even if cred(P) = 0.5 (undecidable), we can still:

1. **Combine**: cred(P ∧ Q) = cred(P) * cred(Q) = 0.25
2. **Negate**: cred(~P) = 0.5
3. **Condition**: cred(Q | P) via chain rule
4. **Bound**: cred(P) ∈ [0.4, 0.6] with partial evidence

The undecidable value participates in reasoning.

## Open Questions

1. Can we characterize which statements have cred exactly 0.5?
2. Is there a hierarchy of undecidability degrees in Cred?
3. How does independence (unconstrained) differ from undecidability (0.5)?
4. Can forcing (set theory) be understood as credence manipulation?
