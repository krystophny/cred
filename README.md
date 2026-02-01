# Probabilistic Foundations

[![Build Papers](https://github.com/krystophny/foundations/actions/workflows/build-papers.yml/badge.svg)](https://github.com/krystophny/foundations/actions/workflows/build-papers.yml)
[![Lean Build](https://github.com/krystophny/foundations/actions/workflows/lean.yml/badge.svg)](https://github.com/krystophny/foundations/actions/workflows/lean.yml)

An alternative axiomatization of mathematics using **probability as the primitive notion**, with classical logic emerging as the degenerate {0,1} boundary case.

## Papers

Download PDFs from the [latest build artifacts](https://github.com/krystophny/foundations/actions/workflows/build-papers.yml) (click the latest successful run, then download the `papers` artifact).

| Paper | Title | Status |
|-------|-------|--------|
| 1 | [Classical Logic as the {0,1} Boundary Case](papers/paper1-classical-logic/main.tex) | Draft |
| 2 | [Probabilistic Proof Theory](papers/paper2-proof-theory/main.tex) | Draft |
| 3 | [Probabilistic Natural Numbers](papers/paper3-natural-numbers/main.tex) | Draft |
| 4 | [Zorn's Lemma via Distributions](papers/paper4-zorn-no-choice/main.tex) | Draft |
| 5 | Synthetic Probability Type Theory | Planned |
| 6 | Markov Categories for Probabilistic Reasoning | Planned |

## Key Ideas

1. **Probability is primitive**: We axiomatize `Prob` directly, not via measure theory on top of set theory on top of logic.

2. **Classical logic is derived**: The logical operations (AND, OR, NOT) are probability algebra restricted to {0,1}. LEM is an algebraic identity, not an axiom.

3. **Graded entailment**: `Γ ⊢[p] φ` means "derive φ from Γ with confidence at least p". Classical entailment is the p=1 case.

4. **Existence via distributions**: Probabilistic Zorn asserts distributions over near-maximal elements exist, avoiding the selection problem that requires AC in classical Zorn.

## Building

### Lean formalization

```bash
cd lean && lake build
```

### Papers (requires LaTeX)

```bash
cd papers/paper1-classical-logic && pdflatex main.tex
```

Or use the GitHub Actions workflow which builds all papers automatically.

## Project Structure

```
foundations/
├── lean/
│   ├── Foundations.lean    # Main Lean 4 formalization
│   ├── lakefile.lean       # Build configuration
│   └── lean-toolchain      # Lean version (4.14.0)
├── papers/
│   ├── paper1-classical-logic/
│   ├── paper2-proof-theory/
│   ├── paper3-natural-numbers/
│   └── paper4-zorn-no-choice/
└── README.md
```

## Current Status

- **Axioms**: 48 (Prob type, conditional expectation, countable sum, probabilistic Zorn)
- **Theorems**: 33 (all machine-verified)
- **Build**: Zero warnings, zero errors

The framework is axiomatized, not constructed. Paper 5 aims to provide a synthetic construction of `Prob` from type-theoretic primitives, which would turn many axioms into theorems.

## Philosophy

This is not a claim that probability is "more fundamental" than logic in an absolute sense. Both are valid starting points. The advantages of the probability-first approach:

- Uncertainty is native, not retrofitted
- Graded truth values are primitive
- Some existence proofs become constructive (distributions vs. points)
- The framework naturally supports probabilistic reasoning

The classical embedding (Papers 1-3) is a **consistency check**: it shows standard mathematics is recoverable. The interesting work happens in the full [0,1] setting, especially Paper 4's treatment of Zorn's lemma.

## License

MIT
