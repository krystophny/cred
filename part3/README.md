# Part 3: New Techniques, Undecidability, and Self-Hosting

What becomes possible when truth is graded and self-reference works.

## The Opportunities

### 1. Self-Negating Reference Works
Binary logic: Self-negating sentences → paradoxes.

Cred: Self-negating sentences → fixed points. The liar sentence ("This is false") has cred = 0.5.

### 2. No Ex Falso
Binary logic: From contradiction, anything follows.

Cred: Conditioning on impossibility is unconstrained, not trivially true.

### 3. Metareasoning
Cred's handling of self-reference enables certain forms of metareasoning about uncertainty that binary systems cannot express.

## Files

- `01-asymptotic-proofs.md` — Proofs approaching certainty
- `02-fixed-points.md` — Self-reference and paradox dissolution
- `03-undecidability.md` — Working with cred = 0.5 statements
- `04-new-techniques.md` — Proof techniques unique to Cred
- `05-open-questions.md` — Research directions including self-hosting

## Key Ideas

### Fixed Points for Self-Negation
```
cred(L) = ~cred(L) implies cred(L) = 0.5
```
Self-negating sentences (like the liar) find a stable fixed point credence.

### Godel Still Applies
Godel's incompleteness is about provability, not truth. The sentence "G is not provable in S" is NOT self-negating (unprovable is not false). If Cred is extended to express arithmetic, Godel's theorem applies. Cred handles the liar sentence; it does not dissolve Godel.

### Chain Rule Semantics
```
cred(A | B) * cred(B) = cred(A AND B)
When cred(B) = 0: any value satisfies the chain rule
```
This semantic property blocks ex falso without syntactic restrictions.

## The Big Picture

Binary logic encounters:
- Self-negating paradoxes (liar sentence breaks boolean assignment)
- Ex falso quodlibet (from contradiction, anything follows)
- Undefined conditioning (P(A|B) undefined when P(B)=0)

Cred handles these differently:
- Self-negating sentences have fixed point cred = 0.5
- No ex falso (conditioning on 0 is unconstrained, not trivially true)
- Conditioning always syntactically valid (though semantically inert at 0)

**Important:** Godel, Tarski, and the halting problem apply to ANY sufficiently powerful formal system. Cred, if extended to express arithmetic, would be subject to the same limitations. Cred's innovation is in handling self-negation and blocking ex falso, not in escaping fundamental computability limits.
