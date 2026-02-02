# Proposal: Credence Foundation for Mathematics

## What the Literature Search Found

**No existing foundation makes credence/probability primitive with logic emergent.**

But we have strong prior art:

| Prior Art | What It Gives Us |
|-----------|------------------|
| **Krantz et al. (1971)** | Qualitative probability — no numbers needed |
| **De Finetti (1931)** | Probability as primitive (not derived from logic) |
| **Pavelka-Hajek (1979-1998)** | Graded provability: Γ ⊢ A @ c |
| **Markov Categories (2020)** | Synthetic probability, conditioning |
| **Paraconsistent logic** | Non-explosive foundations |

**Our contribution**: Synthesize these into a foundation where LOGIC EMERGES.

---

## The Minimal Structure

### Do We Need Bayes Rule?

**Bayes**: P(A|B) = P(A∧B) / P(B)

This requires division. We can avoid it:

**Chain Rule** (multiplicative): P(A,B) = P(A|B) · P(B)

This only needs multiplication (*). No division at foundation level.

### Do We Need Addition (+) for Marginalization?

**Marginalization**: P(A) = Σ_b P(A,b)

This requires addition over potentially infinite values.

**Options**:
1. **No addition**: Use only De Morgan algebra (*, ~, ≤). Addition is derived: a + b := ~(~a * ~b). This is sufficient for logic but not full probability.

2. **Add true addition**: Get full probability theory but more axioms.

**Recommendation**: Start minimal (De Morgan only). Add true + later if needed.

### The Minimal Axiom Set

```
PRIMITIVE:
  C : set of credence values
  0, 1 : C (impossibility, certainty)
  * : C → C → C (conjunction)
  ~ : C → C (complement)
  ≤ : C → C → Prop (ordering)

AXIOMS:
  c * 1 = c                    (identity)
  c * 0 = 0                    (annihilation)
  (a * b) * c = a * (b * c)    (associativity)
  a * b = b * a                (commutativity)
  ~~c = c                      (involution)
  ~0 = 1, ~1 = 0               (complement bounds)
  a ≤ b → ~b ≤ ~a              (antitone)
  0 ≤ c ≤ 1                    (bounded)

DERIVED:
  a + b := ~(~a * ~b)          (De Morgan OR)
  a ⇒ b := ~a + b              (implication)
```

**This is a De Morgan algebra. No numbers assumed.**

---

## Formalizing Without Logic (But With Meta-Logic)

### The Key Distinction

```
META-LEVEL (how we talk about the system):
  We use classical logic, set theory, whatever.
  This is for US as mathematicians.

OBJECT-LEVEL (the system itself):
  Credence spaces. No logic assumed.
  Logic EMERGES as the {0,1} collapse.
```

### Why This Is Legitimate

- Gödel used Peano arithmetic at meta-level to study formal systems
- Tarski used set theory at meta-level for semantics
- We use logic at meta-level to define credence foundation

**The meta-level doesn't make logic foundational in the object theory.**

### The Construction

```
META: We (using logic) define:

OBJECT:
  1. Credence algebra C (the axioms above)
  2. Terms T (untyped lambda calculus or similar)
  3. Credence assignment: cred : T → C
  4. Propagation rules: cred(f a) = cred(f) * cred(a), etc.
  5. Types := credence predicates T → C
  6. Logic := what happens when C = {0,1}
```

---

## Credence Before Numbers

### Qualitative Probability (Krantz et al.)

Start with ONLY ordering:
```
A ≥ B means "A is at least as credible as B"
```

**Axioms** (simplified):
1. ≥ is transitive and total
2. Certainty ≥ A ≥ Impossibility for all A
3. Additivity via ordering (if disjoint, can compare sums)
4. Archimedean (no infinitely more credible events)

**Representation Theorem**: There exists a unique function P: Events → [0,1] such that A ≥ B iff P(A) ≥ P(B).

**Numbers EMERGE from the ordering.**

### The Hierarchy

```
Layer 0: Qualitative ordering (≥)
         ↓ representation theorem
Layer 1: Numbers [0,1] (emerge as representation)
         ↓ add operations
Layer 2: De Morgan algebra (*, ~)
         ↓ terms + credence assignment
Layer 3: Credence spaces
         ↓ collapse to {0,1}
Layer 4: Logic (emerges)
         ↓ propositions-as-types
Layer 5: Type theory (emerges)
         ↓
Layer 6: Mathematics
```

---

## Asymptotic/Weak Proofs

### Classical Proof
```
A proof of P is a finite witness that P is TRUE.
Binary: proven or not proven.
```

### Credence Proof
```
A proof of P is a process that makes cred(P) approach 1.
Continuous: degree of proven-ness.
```

### Degrees

| Limit | Status |
|-------|--------|
| cred → 1 | Proven |
| cred → 1 - ε | Almost proven (high confidence) |
| cred → c ∈ (0,1) | Partially established |
| cred → ε | Almost refuted |
| cred → 0 | Refuted |
| No limit | Undecidable (oscillates) |

### Asymptotic Theorems

```
Theorem (asymptotic): lim_{n→∞} cred(P_n) = 1

This is WEAKER than: cred(P) = 1
But STRONGER than: P is unprovable
```

**New category of mathematical truth**: asymptotically true.

---

## Avoiding Explosion

### The Problem

Classical logic: A ∧ ¬A ⊢ B (from contradiction, anything follows)

### Credence Solution

```
cred(A ∧ ~A) = cred(A) * (1 - cred(A))

Maximum at cred(A) = 0.5: cred(A ∧ ~A) = 0.25
```

**A contradiction has credence at most 0.25, not 1.**

```
cred(B | A ∧ ~A) = cred(A ∧ ~A ∧ B) / cred(A ∧ ~A)
                 = something / 0.25
                 ≠ 1 in general
```

**From a contradiction, you DON'T get everything with certainty.**

### Ex Falso

```
When cred(A) = 0:
cred(B | A) = cred(A ∧ B) / cred(A) = 0 / 0 = UNDEFINED
```

**NOT "anything follows with certainty."**
**Rather: "the question is undefined."**

This is **cleaner** than classical ex falso.

---

## The Instances

### Instance 1: Boolean (Logic)
```
C = {0, 1}
* = AND
~ = NOT
≤ = standard
```
**Result**: Classical propositional logic.

### Instance 2: Unit Interval (Probability)
```
C = [0, 1]
* = multiplication
~ c = 1 - c
≤ = standard
```
**Result**: Probability theory.

### Instance 3: Łukasiewicz
```
C = [0, 1]
a * b = max(0, a + b - 1)
~ c = 1 - c
```
**Result**: Many-valued logic.

**All are instances of the same foundation.**

---

## Summary: The Proposal

### What We Build

```
FOUNDATION: Credence Spaces
  - Qualitative ordering (no numbers)
  - De Morgan algebra (*, ~, ≤)
  - Terms with credence assignment
  - Types as credence predicates

EMERGENT: Logic
  - Collapse to {0,1}
  - Propositions as predicates
  - Proofs as credence-1 terms

EMERGENT: Mathematics
  - Numbers (credence-1 terms satisfying axioms)
  - Sets (credence predicates)
  - Functions (credence-preserving maps)
```

### What We Avoid

- Logic as foundation (it emerges)
- Explosion (credence-bounded contradictions)
- Binary proofs (asymptotic truth)
- Numbers as primitive (emerge from ordering)

### What We Gain

- Unified foundation for logic AND probability
- Graded truth (handles uncertainty)
- Clean ex falso (undefined, not explosive)
- Paradoxes dissolve (fixed points at 0.5)

---

## Next Steps

1. **Formalize qualitative axioms** (in meta-logic, defining object theory)
2. **Prove representation theorem** (numbers emerge)
3. **Define credence spaces** (terms + credence)
4. **Show logic emerges** (Boolean collapse)
5. **Build basic mathematics** (numbers, sets, functions)
6. **Demonstrate paradox resolution** (liar, Gödel, Russell)
