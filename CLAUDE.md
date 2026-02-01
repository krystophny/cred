# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

Research project exploring **probability as a foundational system for mathematics**, with classical logic derived as the degenerate {0,1} case. The goal is to replace logic with probability theory as the primitive, machine-verified from the ground up.

## Build Commands

```bash
cd lean && lake build
```

## Architecture

### Meta-Level vs Object-Level Separation

The critical discipline is separating:
- **Metalogic** (Lean's type theory): Used ONLY to define and verify the probabilistic system
- **Object system** (probabilistic foundations): Where actual mathematics happens, using ONLY probabilistic primitives

```
METALOGIC: Lean's Type Theory (specification language)
              │ defines
              ▼
OBJECT SYSTEM: Probabilistic Foundations (Prob, 𝔼[·|·], ⊢[p])
              │ contains
              ▼
CLASSICAL LOGIC: The {0,1} boundary case
```

### Core Primitives (Object Level)

All object-level theorems must use ONLY:
- `Prob` type with operations (`+ₚ`, `*ₚ`, `-ₚ`, `≤ₚ`, `𝟘`, `𝟙`)
- `𝔼[f | g]` conditional expectation
- `Γ ⊢[p] φ` probabilistic entailment (meaning `p ≤ₚ 𝔼[φ | Γ]`)
- Derived notions built from these

### Logic Slippage Prevention

**Lean's logical connectives (∧, ∨, →, ¬, ∀, ∃) must NEVER appear at the object level** except when explicitly deriving them as the {0,1} special case.

Red flags:
- `∀ x, P x → Q x` at object level (should be probabilistic)
- `∃ x, P x` at object level (should be `𝔼[indicator] > 𝟘`)
- `A ∧ B` at object level (should be `prob_and A B` or `A ∧ₚ B`)

Lean logic is permitted ONLY for:
- Defining what probabilistic primitives ARE
- Metatheorems ABOUT the probabilistic system
- Proof automation internals

### Key Concepts

- **Probabilistic entailment**: `Γ ⊢[p] φ` means `p ≤ₚ 𝔼[φ | Γ]`
- **Cut rule**: `(Γ ⊢[p] φ) → (φ ⊢[q] ψ) → (Γ ⊢[p*q] ψ)`
- **Strong negation**: `∀ψ, 𝔼[φ | ψ] = 𝟘` (measure zero)
- **Weak negation**: `¬ₚ φ = fun x => 𝟙 -ₚ φ x` (pointwise complement)
- **Classical logic**: restriction to `{0,1}`-valued `ProbProp`
- **LEM as algebra**: `φ x +ₚ (¬ₚ φ) x = 𝟙` (algebraic identity, not logical axiom)

## File Structure

```
lean/
  lakefile.lean      # Lake build configuration
  Foundations.lean   # Main Lean 4 formalization
```

## Current Status

All phases implemented. Build: `cd lean && lake build` (zero warnings).

### Phases A-C: Core Framework (COMPLETE)
- `Prob` type: ordered semiring in [0,1]
- `𝔼[f|g]`: conditional expectation primitive
- `Γ ⊢[p] φ`: probabilistic entailment
- Proof theory: `axiom_rule`, `weaken`, `cut_rule`, `mono_rule`
- Classical logic as {0,1} restriction

### Phase D: Probabilistic Zorn (COMPLETE)
- `ProbPoset`: probabilistic partial order with `P.le x y`
- `prob_lt`: strict ordering `P(x ≤ y) * (1 - P(y ≤ x))`
- `NearMaximal`: `∀y, prob_lt P x y ≤ ε`
- `ChainComplete`: every chain has an upper bound
- `prob_zorn`: chain-complete posets have distributions on near-maximals (axiom)
- `classical_zorn_from_prob`: classical Zorn as {0,1} special case

### Phase E: Natural Numbers (COMPLETE)
- `prob_sum`: countable summation primitive
- `ProbNat`: distributions over Nat (exhaustive + disjoint)
- `prob_succ_is_n`: successor shifts distribution
- `peano1`: zero is not a successor
- `peano2_shift`: successor is injective
- `det_nat`: deterministic natural numbers

### Phase F: More Proof Rules (COMPLETE)
- Implication: `prob_implies_refl_classical`, `prob_modus_ponens_classical`
- Structural: `prob_and_comm`, `prob_and_assoc`, `prob_exchange`, `prob_contraction`
- Negation: `strong_neg_and`, `strong_neg_implies_weak_one`
- De Morgan: `prob_de_morgan_and`, `prob_de_morgan_or`
- Identity/absorption: `prob_or_zero/one`, `prob_and_zero/one`

## Implementation Notes

- Lean 4 v4.14.0 (see `lean/lean-toolchain`)
- Probability is axiomatized (not constructed from measure theory)
- Conditional expectation `𝔼[_|_]` is the core primitive
- Classical logic operations (`∧ₚ`, `∨ₚ`, `¬ₚ`) are `noncomputable` (depend on axiom operations)
