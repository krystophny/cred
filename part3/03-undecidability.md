# Working with Incompleteness and Underdetermination

This note is intentionally conservative: Part 1 does **not** contain a formal theory that assigns credences to mathematical statements from proofs. It provides an algebra on `[0,1]` and a primitive conditioning constraint. Anything that connects “provability in a system” to “credence” is additional structure.

## Three Different Notions (Do Not Conflate)

### 1) Algebraic fixed points (forced)

If a credence value satisfies a self-negating equation,
```
c = ~c
```
then (in the real-valued model) `c = 0.5`. This is the mechanism behind the liar fixed point in Part 1.

This has nothing to do with Gödel incompleteness; it is a fixed point of the negation map on `[0,1]`.

### 2) Epistemic ignorance (chosen)

You might choose a prior like `cred(P)=0.5` to represent “no evidence either way”. This is a modelling choice, not a theorem.

### 3) Proof-theoretic incompleteness / independence (meta-theoretic)

Statements like CH being independent of ZFC mean (roughly) that ZFC neither proves CH nor proves ¬CH. This does **not** force any particular numerical credence in Cred.

In particular:
- “independent of axioms” is not the same thing as “unconstrained” in Cred,
- because “unconstrained” has a precise technical meaning tied to the conditioning equation at evidence `0`.

## What “Unconstrained” Means in Cred

In Part 1, “unconstrained” refers to the chain rule constraint:
```
cred(A|B) ⊗ cred(B) = cred(A ∧ B)
```
When `cred(B)=0`, the equation becomes `x ⊗ 0 = 0`, which is satisfied by any `x` (provided the joint is `0`). That is a statement about an equation, not about axioms being incomplete.

## How One Might Relate Theories and Credences (Future Work)

If we want to talk about “credence in CH given ZFC”, we need to define how proof-theoretic or model-theoretic information supplies constraints on credence assignments. For example, one could imagine a principle of the form:
- if a theory `T` proves `P`, then `cred(P|T)=1`,

but spelling this out requires (at least) a formal notion of what `T` is as “evidence”, and how joints like `cred(P ∧ T)` are supplied. None of that is in Part 1 yet.

## Practical Takeaway

Part 1 gives a rigorous, Lean-checked algebra for manipulating credence values once they are assigned (and for understanding when conditioning is determined or underdetermined). It does not turn incompleteness results into specific numbers like `0.5`.

## Open Questions

1. What additional principles connect proof objects (or models) to credence constraints without reintroducing explosion?
2. Is there a useful notion of “credence not determined by theory T” that is distinct from evidence-0 underdetermination?
3. Which fixed points beyond `c = ~c` matter for self-reference in richer settings?
