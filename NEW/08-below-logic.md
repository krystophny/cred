# Below Logic: Credence as Pre-Logical Foundation

## The Vision

You want:
1. **NOT** logic with credences attached
2. **NOT** type theory with weights
3. Something **MORE PRIMITIVE** than logic
4. Logic EMERGES as the {0,1} degenerate case
5. "Proof" = asymptotically approaching credence 1
6. Ex falso is NATURAL, not a paradox

## The Hierarchy (Your Vision)

```
Layer -1: Credence Space (PRE-LOGICAL)
          ↓ (degeneration to endpoints)
Layer 0:  Logic (emerges as {0,1} limit)
          ↓ (propositions-as-types)
Layer 1:  Type Theory (emerges from logic)
          ↓ (sets-as-types)
Layer 2:  Mathematics (built on types)
```

Current foundations start at Layer 0 or 1. You want to start at Layer -1.

## What "Below Logic" Means

### Logic Has Binary Truth
```
P is TRUE  or  P is FALSE
No middle ground. No "almost true."
```

### Below Logic: Continuous Credence
```
P has credence c ∈ [0, 1]
c = 1: certain (what logic calls "true")
c = 0: impossible (what logic calls "false")
0 < c < 1: intermediate (logic cannot express this)
```

### Logic Emerges When Credences Collapse
```
When we FORCE credences to {0, 1}:
- Intermediate states disappear
- We get classical logic
- Ex falso becomes paradoxical
- Gödel sentences become undecidable (no c = 0.5)
```

## The Pre-Logical Primitives

### Primitive 1: Credence Values
```
C = [0, 1] with:
- Multiplication: c · d (conjunction)
- Complement: ~c = 1 - c (negation)
- Order: c ≤ d (implication of sorts)
```

### Primitive 2: Terms (Unstructured)
```
Terms exist. They're just... things.
No types. No logical classification.
Just entities that can have credence.
```

### Primitive 3: Credence Assignment
```
cred : Term → C
Every term has a credence value.
```

### Primitive 4: Operations on Credence
```
cred(f a) = cred(f) · cred(a)    -- application multiplies
cred(~t) = ~cred(t)              -- negation complements
cred(a, b) = cred(a) · cred(b)   -- pairing multiplies
```

## Asymptotic Truth

### What Is "Proof" in This Foundation?

**Old (Logic)**: A proof is a finite witness that P is TRUE.

**New (Credence)**: A proof is a PROCESS that makes cred(P) approach 1.

```
P is "proven" if: lim_{n→∞} cred_n(P) = 1
P is "refuted" if: lim_{n→∞} cred_n(P) = 0
P is "undecidable" if: lim_{n→∞} cred_n(P) = c ∈ (0, 1)
```

### Asymptotic Implication

```
P ⟹ Q  means:  cred(Q | P) = lim cred(P ∧ Q) / cred(P) = 1
```

Not "if P then Q" but "as P becomes certain, Q becomes certain."

### Degrees of Proof

| cred(P) | Status |
|---------|--------|
| 1 | Proven (certain) |
| 1 - ε | Almost proven (high confidence) |
| 0.5 | Undecidable / maximally uncertain |
| ε | Almost refuted |
| 0 | Refuted (impossible) |

## Ex Falso: Natural, Not Paradoxical

### The Problem with Classical Ex Falso
```
⊥ → P  is TRUE for any P
"From false, anything follows"
This seems wrong: why should impossibility give certainty?
```

### Ex Falso in Credence Foundation
```
If cred(A) = 0, then cred(A → B) = ?

Using: cred(A → B) = ~cred(A) + cred(A) · cred(B)
                   = 1 - 0 + 0 · cred(B)
                   = 1

So A → B has credence 1 when A has credence 0.
```

**But this is VACUOUS, not EXPLOSIVE.**

The key insight:
```
cred(B | A) = cred(A ∧ B) / cred(A)
When cred(A) = 0, this is 0/0 = UNDEFINED
```

**True conditioning is undefined when the condition is impossible.**
This is cleaner than "from false, derive anything with certainty."

### Graded Ex Falso
```
As cred(A) → 0:
- cred(A → B) → 1 (vacuously)
- cred(B | A) → undefined
- Conclusions become UNCONSTRAINED, not CERTAIN
```

| cred(A) | cred(B \| A) | Interpretation |
|---------|-------------|----------------|
| 1 | determined by evidence | fully constrained |
| 0.5 | weakly constrained | partial evidence |
| ε | almost unconstrained | minimal evidence |
| 0 | UNDEFINED | no evidence (ex falso) |

## Logic Emerges as Degeneration

### The Forcing Function
```
force : C → {0, 1}
force(c) = 1 if c > 0.5
force(c) = 0 if c < 0.5
force(0.5) = ??? (undecidable)
```

### What Happens When We Force

| Pre-Logical | After Forcing |
|-------------|---------------|
| cred(P) = 0.7 | P is TRUE |
| cred(P) = 0.3 | P is FALSE |
| cred(P) = 0.5 | UNDECIDABLE |
| cred(P) · cred(Q) | P ∧ Q |
| ~cred(P) | ¬P |

### Why Logic Looks Paradoxical

Classical logic has paradoxes (ex falso, liar, Gödel) because:
- It only sees {0, 1}
- Intermediate states are invisible
- The liar "This is false" has cred = 0.5, but logic can't express 0.5
- Gödel's G has cred(G) = 0.5, but logic sees it as undecidable

**Logic is a lossy compression of credence structure.**

## Building Mathematics on Credence

### Numbers
```
Numbers are terms with credence 1 (certain existence).
0, 1, 2, ... have cred = 1.
Imaginary numbers initially had cred < 1 (controversial).
Infinitesimals have cred depending on your framework.
```

### Sets
```
A set S is a credence predicate: S : Term → C
x ∈ S means cred(S(x)) > threshold
Fuzzy set membership is NATURAL, not an extension
```

### Functions
```
f : A → B means:
For all a with cred(a) = c, cred(f(a)) ≥ c · k
(functions preserve or reduce credence)
```

### Proofs
```
A proof of P is a term t such that:
cred(t : P) → 1 (asymptotically)

A refutation is a term showing:
cred(P) → 0 (asymptotically)
```

## Comparison to Existing Foundations

| Foundation | Primitive | Truth | Proof |
|------------|-----------|-------|-------|
| Set Theory (ZFC) | Sets, ∈ | Binary | Finite derivation |
| Type Theory (MLTT) | Types, terms | Binary | Term of type |
| Logic | Propositions | Binary | Derivation tree |
| **Credence Foundation** | Credence | Continuous | Asymptotic limit |

## The Radical Claim

**Logic is not fundamental. Logic is what credence looks like when you squint.**

When you force [0,1] to {0,1}:
- Graded truth becomes binary
- Ex falso becomes paradoxical
- Gödel becomes undecidable
- Self-reference becomes problematic

**Mathematics built on credence would be:**
- More expressive (intermediate truth values)
- Cleaner (ex falso is natural)
- More honest (undecidability is visible as 0.5)
- Continuous (logic is a limit)

## Open Questions

1. **Computation**: What does "compute" mean in credence foundation?
2. **Infinity**: How do infinite processes relate to limits of credence?
3. **Self-reference**: Does cred(G) = 0.5 fully resolve Gödel?
4. **Axiom of Choice**: What credence does AC have?
5. **Consistency**: Is credence foundation consistent? (What does that mean?)

## Next Steps

To build this:
1. Formalize credence spaces (not type theory!)
2. Define "proof" as asymptotic credence
3. Show logic emerges as {0,1} collapse
4. Rebuild basic mathematics (numbers, sets, functions)
5. Demonstrate cleaner treatment of paradoxes
