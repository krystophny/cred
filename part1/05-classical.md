# Adding Ex Falso: Classical Logic (Optional)

## From Relevant to Classical

Boolean Cred gives relevant logic. To get classical logic, we must ADD material implication.

```
Boolean Relevant Logic
         ↓
         ↓ ADD: A → B := ~A OR B
         ↓
Classical Propositional Logic
```

This is an **additional assumption**, not a natural consequence.

## What Material Implication Adds

```
A → B := ~A OR B
```

Properties gained:
- Ex falso: ⊥ → A = ~⊥ OR A = 1 OR A = 1 ✓
- A → (B → A) = 1 (true proposition implied by anything) ✓
- ~A → (A → B) = 1 (false proposition implies anything) ✓

These are the "paradoxes of material implication."

## Why You Might Want Classical Logic

1. **Familiarity**: Most mathematicians trained in classical logic
2. **Simplicity**: Material implication is truth-functional
3. **Existing mathematics**: Most theorems proven classically
4. **Tooling**: Proof assistants mostly use classical logic

## Why You Might NOT Want It

1. **Ex falso is strange**: Why should impossibility imply everything?
2. **Relevance lost**: Premises don't need to connect to conclusions
3. **Explosion**: One contradiction destroys entire theory
4. **Unrestricted comprehension fails**: Need set theory restrictions (ZFC)

## The Trade-Off

| Feature | Relevant (Cred) | Classical |
|---------|-----------------|-----------|
| Ex falso | No | Yes |
| Paradoxes of implication | No | Yes |
| Unrestricted comprehension | Yes (contained) | No (Russell) |
| Relevance | Enforced | Not enforced |
| Familiar | Less | More |

## How to Add Ex Falso

If you want classical logic, add:

**Axiom (Ex Falso)**:
```
(A | ⊥) = 1    for all A
```

This forces the unconstrained case to be "true."

Alternatively, define material implication as primitive:
```
A → B := ~A OR B
```

And use → instead of conditioning.

## The Full Picture

```
Cred [0,1]
    ↓ Boolean collapse
Relevant Logic (no ex falso)
    ↓ ADD ex falso axiom
Classical Propositional Logic
    ↓ add quantifiers
Classical FOL
    ↓ add set axioms (restricted comprehension)
ZFC
    ↓
Classical Mathematics
```

Each downward step is an ADDITION of structure/axioms, not a natural consequence.

## Our Position

We work primarily in Cred (graded) or its Boolean collapse (relevant logic).

Classical logic is available as an **optional extension** for compatibility with existing mathematics, but it's not the primary foundation.

```
Primary:   Cred [0,1] → Relevant Logic
Optional:  Relevant Logic + Ex Falso → Classical
```

## Historical Note

Classical logic came first historically, so it seems "natural." But:

- Relevant logic (1960s) showed ex falso is rejectable
- Probability theory (always) has undefined conditioning at zero
- Paraconsistent logic (1970s) showed explosion is avoidable

Classical logic is a **choice**, not a necessity.
