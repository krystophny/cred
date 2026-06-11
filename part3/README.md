# Part 3: Paradox Without Explosion

Part 1 establishes the constraint algebra. Part 2 adds interpretation, consequence relations, and update rules. Part 3 studies crisp recovery, paradox solution sets, graded comprehension, and external conditioning.

## Files

- `paper.tex`: working Part 3 paper: crisp fragments, solution sets, graded comprehension, and external conditioning
- `01-asymptotic-proofs.md`: proofs approaching certainty (cred -> 1)
- `02-fixed-points.md`: self-reference and paradox dissolution
- `03-undecidability.md`: incompleteness and underdetermination (distinct from the 1/2 fixed point)
- `04-proof-patterns.md`: proof patterns enabled by the credence algebra
- `05-open-questions.md`: research directions including self-hosting
- `06-graded-mathematics.md`: building mathematics (arithmetic, analysis, set theory) on graded foundations

## Build

```bash
cd part3 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

## Deferred from Part 2

The following topics were originally in Part 2 but belong here because they require the full machinery of Parts 1 and 2:

- **Graded proofs**: what it means to "prove" something when truth is graded (convergence to credence 1 vs. partial evidence). Covered in `01-asymptotic-proofs.md`.
- **Graded mathematics**: building arithmetic, analysis, and set theory on graded predicates. Covered in `06-graded-mathematics.md`.
- **Self-hosting**: using the credence algebra to reason about the credence algebra itself, enabled by self-reference handling. Related material in `02-fixed-points.md` and `05-open-questions.md`.

## Key distinctions

1. **Self-negation vs. incompleteness**: the liar sentence (c = ~c, forced to 1/2) is algebraic. Godel incompleteness (unprovable ≠ false) is proof-theoretic. The credence algebra handles the first; the second applies to any system strong enough to encode arithmetic. See `03-undecidability.md`.

2. **Unconstrained vs. undecidable**: "unconstrained" in Part 1 means the chain rule imposes no constraint when evidence is zero. "Undecidable" means a formal system neither proves nor refutes. These are different notions. See `03-undecidability.md`.

3. **Proof vs. evidence**: classical proof establishes credence 1 exactly. Asymptotic proof converges to 1. Partial evidence gives intermediate credence. All three are meaningful but distinct. See `01-asymptotic-proofs.md`.
