# Layer 0: Credence Algebra

## The Primitive Structure

Everything begins with a **De Morgan algebra**:

```
C = (C, 1, 0, *, ~, ≤)

where:
  C     : Set                    -- carrier (credence values)
  1     : C                      -- certainty
  0     : C                      -- impossibility
  *     : C → C → C              -- conjunction/multiplication
  ~     : C → C                  -- negation/complement
  ≤     : C → C → Prop           -- ordering
```

## Axioms

### Multiplication (*, 1, 0)
```
c * 1 = c                        -- identity
c * 0 = 0                        -- annihilation
(a * b) * c = a * (b * c)        -- associativity
a * b = b * a                    -- commutativity
```

### Complement (~)
```
~0 = 1                           -- complement of impossibility
~1 = 0                           -- complement of certainty
~~c = c                          -- involution
```

### Order (≤)
```
c ≤ c                            -- reflexivity
a ≤ b ∧ b ≤ c → a ≤ c            -- transitivity
a ≤ b ∧ b ≤ a → a = b            -- antisymmetry
0 ≤ c                            -- 0 is least
c ≤ 1                            -- 1 is greatest
```

### De Morgan Laws
```
~(a * b) = ~a + ~b               -- where a + b := ~(~a * ~b)
```

## Derived Operations

### Disjunction (Addition)
```
a + b := ~(~a * ~b)              -- De Morgan dual of *
```

### Implication (Conditioning)
```
a ⇒ b := ~a + b                  -- material implication
       = ~(a * ~b)               -- equivalently
```

**Note**: This is NOT the foundation's primary connective.
The primary operation is *, not ⇒.

## Key Instances

### Instance 1: Boolean (Classical Logic)
```
C = {0, 1}
* = AND
~ = NOT
+ = OR
≤ = standard ordering
```

This gives classical propositional logic.

### Instance 2: Unit Interval (Probability)
```
C = [0, 1] ⊂ ℝ
* = multiplication
~ c = 1 - c
+ = probabilistic sum: a + b - a*b
≤ = standard ordering
```

This gives probabilistic reasoning.

### Instance 3: Łukasiewicz Algebra
```
C = [0, 1]
a * b = max(0, a + b - 1)        -- Łukasiewicz t-norm
~ c = 1 - c
```

This gives Łukasiewicz many-valued logic.

## What We Have So Far

At this layer, we have:
- Credence values (elements of C)
- Operations on credences (*, ~, +, ⇒)
- An ordering on credences (≤)

We do NOT have:
- Terms
- Types
- Judgments
- Contexts

These will be built in subsequent layers.

## The Key Insight

In standard type theory, we have:
```
Types → Propositions → Truth values
```

In CredTT v2, we reverse this:
```
Credence values → Propositions (as credence predicates) → Types (as equivalence classes)
```

The credence algebra is the **foundation**. Everything else is **derived**.
