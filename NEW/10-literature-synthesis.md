# Literature Synthesis: Building Mathematics Below Logic

## The Search Result

**No existing foundation makes probability/credence primitive with logic emergent.**

But substantial prior art exists that we can build upon.

## Key Prior Art

### 1. Qualitative Probability (No Numbers)

**Krantz, Luce, Suppes, Tversky (1971)**: *Foundations of Measurement*

Key insight: Probability can be axiomatized as a **qualitative ordering** (≥) without numbers:
```
A ≥ B means "A is at least as probable as B"
```

**Representation Theorem**: Under mild conditions, this ordering has a unique numerical representation.

**What this gives us**: Credence ordering is PRIMITIVE. Numbers are DERIVED.

### 2. De Finetti: Probability as Primitive

**De Finetti (1931, 1974)**: "PROBABILITY DOES NOT EXIST" (objectively)

- Probability is a **primitive psychological notion**
- Dutch Book theorem: coherent betting satisfies probability axioms
- No logical foundation assumed — just behavioral coherence

**What this gives us**: Probability CAN be taken as primitive, not derived from logic.

### 3. Cox's Theorem: Probability from Consistency

**Cox (1946, 1961)**: Derives probability laws from "plausibility" + consistency requirements.

**Limitation**: Cox assumes classical propositional logic as substrate.

**What this gives us**: The IDEA that probability axioms follow from consistency, but we need to do it WITHOUT assuming logic.

### 4. Pavelka-Hajek: Graded Provability

**Pavelka (1979), Hajek (1998)**: Formulas have degrees of provability.

```
|φ|_T = sup{r | T ⊢ (φ, r)}
```

**What this gives us**: The judgment form `Γ ⊢ A @ c` has precedent.

### 5. Markov Categories: Synthetic Probability

**Fritz (2020)**: Categorical axioms for probability without measure theory.

- Copy/delete morphisms
- Conditioning via disintegration
- Information-theoretic results proved synthetically

**Limitation**: No negation, no internal logic, doesn't make probability foundational to logic.

### 6. Non-Explosive Logics

**Paraconsistent logic (da Costa, 1974)**: Rejects explosion (A ∧ ¬A ⊢ B).

**Minimal logic (Johansson, 1937)**: Rejects both excluded middle AND explosion.

**What this gives us**: Precedent for handling contradictions without explosion.

---

## The Key Question: Bayes Rule and Addition?

### Option A: De Morgan Only (Current CredTT)

```
Operations: *, ~, ≤
Derived: a + b := ~(~a * ~b)  (De Morgan OR)
```

**Sufficient for**:
- Propositional logic
- Chain rule: P(A,B) = P(A|B) * P(B)
- Basic reasoning

**Insufficient for**:
- True marginalization: P(A) = Σ_b P(A,b)
- This requires genuine addition over potentially infinite b

### Option B: Add True Addition

```
Operations: *, +, ~, ≤
With: a + b ≠ ~(~a * ~b) in general
```

**This gives**:
- Marginalization
- Full probability theory
- But also: more structure = more assumptions

### Option C: Qualitative Only (No Numbers)

```
Operations: ≥ (ordering only)
Axioms:
1. A ≥ ∅ (anything at least as probable as impossible)
2. If A ∩ B = ∅, then A ≥ B iff A ∪ C ≥ B ∪ C (additivity via ordering)
3. Transitivity, etc.
```

**This is truly minimal**: No numbers, no operations, just ordering.

**Representation theorem**: Numbers emerge as the unique representation.

### Recommendation: Start Qualitative, Add Structure as Needed

```
Level 0: Qualitative ordering (≥)
Level 1: Add multiplication (*) for conjunction
Level 2: Add complement (~) for negation
Level 3: Derive + via De Morgan
Level 4: (Optional) Add true + for marginalization
```

**Each level is a conservative extension.**

---

## Formalizing WITHOUT Logic

### The Challenge

We usually formalize things IN logic. How to formalize something BENEATH logic?

### The Solution: Meta-Logic vs Object-Theory

```
META-LEVEL: Classical logic (for us to reason about the system)
OBJECT-LEVEL: Credence space (the thing we're building)
```

**This is standard in mathematical logic:**
- Gödel used arithmetic at the meta-level to reason about formal systems
- Tarski used set theory at the meta-level for model theory

**We can use classical logic at the meta-level to define a credence-based object theory.**

### The Key: What's Primitive at Object Level

At the object level (the system we're building):
```
PRIMITIVE:
- Credence values (from some algebra C)
- Ordering on credences (≤)
- Conjunction operation (*)
- Complement operation (~)

DERIVED:
- Disjunction: a + b := ~(~a * ~b)
- Implication: a ⇒ b := ~a + b
- Logic: what happens when C = {0,1}
```

### The Meta-Level Doesn't Contaminate

Using classical logic at the meta-level to DEFINE the object theory is fine:
- Peano arithmetic is defined using logic, but PA is about numbers, not logic
- ZFC is defined using logic, but ZFC is about sets, not logic
- Credence foundation is defined using logic, but it's about credence, not logic

**The claim "credence is more fundamental than logic" is about the OBJECT theory.**

---

## The Minimal Axioms

### Axiom Set 1: Qualitative Probability (Following Krantz et al.)

```
Primitives:
- A set Ω of "possibilities"
- A relation ≥ on subsets of Ω ("at least as probable")

Axioms:
Q1. ≥ is a weak order (transitive, complete)
Q2. A ≥ ∅ for all A
Q3. Ω > ∅ (something is more probable than nothing)
Q4. If A ∩ C = B ∩ C = ∅, then A ≥ B iff A ∪ C ≥ B ∪ C
Q5. Archimedean: no infinitely more probable events
Q6. Solvability: for scales of probability
```

**Theorem**: Under these axioms, there exists a unique probability measure P with A ≥ B iff P(A) ≥ P(B).

**Numbers EMERGE from qualitative structure.**

### Axiom Set 2: De Morgan Credence Algebra

```
Primitives:
- A set C of credence values
- Constants 0, 1 ∈ C
- Binary operation * : C × C → C
- Unary operation ~ : C → C
- Relation ≤ on C

Axioms:
D1. (C, *, 1) is a commutative monoid
D2. c * 0 = 0
D3. ~~c = c (involution)
D4. ~0 = 1, ~1 = 0
D5. (C, ≤) is a bounded lattice with 0 least, 1 greatest
D6. ~ is antitone: a ≤ b implies ~b ≤ ~a
D7. De Morgan: ~(a * b) = ~a + ~b where a + b := ~(~a * ~b)
```

### Axiom Set 3: Credence Spaces

```
Primitives:
- A collection of "terms" T
- A credence algebra C
- A credence assignment cred : T → C

Axioms:
S1. Credence algebra axioms (D1-D7)
S2. cred(f a) = cred(f) * cred(a) (application multiplies)
S3. cred((a, b)) = cred(a) * cred(b) (pairing multiplies)
S4. Additional structural axioms as needed
```

---

## Building Mathematics on Credence

### Numbers

**Definition**: A "number" is a term with credence 1.

```
ℕ = {t ∈ T | cred(t) = 1 and t satisfies Peano-like properties}
```

The Peano axioms become statements about terms with credence 1.

### Sets

**Definition**: A "set" is a credence predicate.

```
S : T → C
x ∈ S means cred(S(x)) > 0
x ∈_c S means cred(S(x)) ≥ c
```

Fuzzy membership is natural, not an extension.

### Proofs

**Definition**: A "proof" of P is a sequence approaching credence 1.

```
(t_n) proves P if lim_{n→∞} cred(t_n : P) = 1
```

**Degrees of proof**:
- cred → 1: proven
- cred → 0: refuted
- cred → c ∈ (0,1): partially established
- no limit: undecidable

### Logic

**Definition**: "Logic" is what credence looks like when C = {0,1}.

```
collapse : C → {0,1}
collapse(c) = 1 if c > 0.5
collapse(c) = 0 if c ≤ 0.5
```

All of propositional/predicate logic emerges from this collapse.

---

## Avoiding Explosion

### Classical Explosion
```
From A ∧ ¬A, derive anything.
```

### Credence Version

```
If cred(A) * cred(~A) = cred(A) * (1 - cred(A)) = c

This is maximized at cred(A) = 0.5, giving c = 0.25.
```

**A contradiction doesn't have credence 1. It has credence ≤ 0.25.**

### Ex Falso

```
cred(A → B) = ~cred(A) + cred(A) * cred(B)

When cred(A) = 0:
cred(A → B) = 1 + 0 = 1
```

**But this is vacuous.** The implication is "empty."

**True conditioning**:
```
cred(B | A) = cred(A * B) / cred(A)
When cred(A) = 0: UNDEFINED (0/0)
```

**This is cleaner**: undefined, not "anything follows."

---

## The Research Program

### Phase 1: Qualitative Foundation (No Numbers)
- Axiomatize credence ordering (≥)
- Prove representation theorem
- Numbers emerge as representation

### Phase 2: Algebraic Structure
- Add * (conjunction)
- Add ~ (complement)
- Derive + (disjunction)

### Phase 3: Terms and Credence Spaces
- Define terms (untyped)
- Assign credences to terms
- Define "types" as credence predicates

### Phase 4: Mathematics
- Define numbers, sets, functions
- Prove basic theorems
- Show logic emerges as {0,1} collapse

### Phase 5: Meta-Theory
- Consistency (what does it mean?)
- Completeness (asymptotic?)
- Relation to other foundations

---

## What Doesn't Exist (Our Contribution)

| Existing | Missing | CredTT Contribution |
|----------|---------|---------------------|
| Qualitative probability | Foundation for logic | Logic from credence collapse |
| Graded provability | Type theory integration | Dependent credence types |
| Non-explosive logics | Graded explosion | Continuous ex falso spectrum |
| Markov categories | Negation | De Morgan structure |
| Fuzzy logic | Conditioning primitive | Chain rule, not implication |

**The synthesis is novel, even if components exist.**
