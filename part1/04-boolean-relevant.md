# Boolean Collapse: Relevant Logic Emerges

## The Boolean Case

When C = {0, 1}:

```
0 = false
1 = true
⊗ = AND
~ = NOT
⊔ = OR (derived: a ⊔ b = ~(~a ⊗ ~b))
```

## Conditioning in Boolean

Chain rule (propositional reading): `cred(A|B) ⊗ cred(B) = cred(A ∧ B)`.

In the Boolean collapse (taking truth values as credences), `cred(A ∧ B)` is just `a ∧ b`, so the equation becomes:

`cred(A|B) ⊗ b = a ∧ b`

```
b = 1: (a | 1) ⊗ 1 = a ∧ 1 = a, so (a | 1) = a
b = 0: (a | 0) ⊗ 0 = a ∧ 0 = 0, satisfied for ANY (a | 0)
```

When the condition is false, the conditional is **unconstrained**.

## What This Is NOT

This is NOT classical propositional logic.

Classical logic has material implication:
```
A → B := ~A ∨ B

Truth table:
A | B | A → B
0 | 0 |   1
0 | 1 |   1
1 | 0 |   0
1 | 1 |   1
```

Note: When A = 0, A → B = 1 regardless of B. This is ex falso.

## What This IS

Boolean Cred has primitive conditioning witnesses constrained by the chain rule:
```
(B | A) constrained by chain rule

"Truth table":
A | B | (B | A)
0 | 0 | unconstrained
0 | 1 | unconstrained
1 | 0 | 0 (from chain rule: (0|1)⊗1 = 0)
1 | 1 | 1 (from chain rule: (1|1)⊗1 = 1)
```

When A = 0, (B | A) is unconstrained, not "true".

## This Is Relevant Logic

Relevant logic (Anderson & Belnap, 1960s) rejects:
- Ex falso quodlibet: ⊥ → A
- Paradoxes of material implication

We get the same behavior:
- (A | ⊥) is unconstrained, not derivably true
- No explosion from contradiction

## What You Can Safely Read Off

In the Boolean collapse, the chain rule gives two robust facts:
1. If `A = 1`, then `(B|A)` is determined and equals `B`.
2. If `A = 0`, then `(B|A)` is underdetermined (many values satisfy the constraint).

This explains precisely why ex falso is not forced: the false/zero antecedent case is not a theorem-producing case; it is a constraint-silent case.

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

Some relevant logics admit nontrivial set theories and have been studied in the literature (e.g. Brady, Weber). Any concrete connection to Cred requires additional semantic choices beyond Part 1.

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

1. **Natural**: Relevant-logical behavior appears from the conditioning constraint, not from a bespoke implication connective.
2. **Semantic**: Ex falso fails because the constraint is silent at evidence 0, not because variables are syntactically restricted.
3. **Graded generalization**: The same mechanism extends from `{0,1}` to `[0,1]` (with intermediate credences).
