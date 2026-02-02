# Boolean Collapse: Relevant Logic Emerges

## The Boolean Case

When C = {0, 1}:

```
0 = false
1 = true
* = AND
~ = NOT
+ = OR (derived: a + b = ~(~a * ~b))
```

## Conditioning in Boolean

Chain rule: (a | b) * b = a * b = a AND b

```
b = 1: (a | 1) * 1 = a AND 1 = a, so (a | 1) = a
b = 0: (a | 0) * 0 = a AND 0 = 0, satisfied for ANY (a | 0)
```

When the condition is false, the conditional is **unconstrained**.

## What This Is NOT

This is NOT classical propositional logic.

Classical logic has material implication:
```
A → B := ~A OR B

Truth table:
A | B | A → B
0 | 0 |   1
0 | 1 |   1
1 | 0 |   0
1 | 1 |   1
```

Note: When A = 0, A → B = 1 regardless of B. This is ex falso.

## What This IS

Boolean Cred has conditioning:
```
(B | A) constrained by chain rule

"Truth table":
A | B | (B | A)
0 | 0 | unconstrained
0 | 1 | unconstrained
1 | 0 | 0 (from chain rule: (0|1)*1 = 0)
1 | 1 | 1 (from chain rule: (1|1)*1 = 1)
```

When A = 0, (B | A) is unconstrained, not "true".

## This Is Relevant Logic

Relevant logic (Anderson & Belnap, 1960s) rejects:
- Ex falso quodlibet: ⊥ → A
- Paradoxes of material implication

We get the same behavior:
- (A | ⊥) is unconstrained, not derivably true
- No explosion from contradiction

## Proof Techniques

All standard proof techniques work EXCEPT ex falso:

| Technique | Works? | Why |
|-----------|--------|-----|
| Modus ponens | ✓ | (B \| A) * A = A ∧ B, if A=1 and (B\|A)=1, then B=1 |
| Proof by contradiction | ✓ | If (⊥ \| ~P) = 1, then ~P = 0, so P = 1 |
| Contrapositive | ✓ | (B \| A) = 1 iff (~A \| ~B) = 1 |
| Case analysis | ✓ | Combine (C \| A) and (C \| ~A) |
| Ex falso | ✗ | (B \| ⊥) is unconstrained, not 1 |

## Relevant Logic Systems

Several relevant logics exist:

| System | Key Feature |
|--------|-------------|
| R | Main relevant logic, Church-Rosser property |
| E | "Entailment", stronger than R |
| T | "Ticket entailment" |
| RM | R-mingle, has ½ value in 3-valued version |

Boolean Cred is closest to R or E.

## Relevant Set Theory

With relevant logic as base, you can build set theory with:
- **Unrestricted comprehension**: {x | φ(x)} exists for any φ
- Russell's set {x | x ∉ x} exists but doesn't explode
- Local contradictions are contained

This is studied (Brady, Weber).

## The Diagram

```
Material implication          Conditioning
A → B := ~A OR B              (B | A) via chain rule
        ↓                              ↓
Ex falso holds                No ex falso
        ↓                              ↓
Classical logic               RELEVANT LOGIC ← Boolean Cred lands here
```

## Why This Matters

1. **Natural**: Relevant logic emerges from credence structure, not syntactic restrictions
2. **Semantic**: Relevance is enforced by chain rule, not variable sharing
3. **Graded generalization exists**: [0,1] Cred generalizes Boolean relevant logic
4. **Set theory works**: Unrestricted comprehension without explosion
