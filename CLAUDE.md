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

All core theorems proved (no `sorry` remaining):

### Proof Theory
- `axiom_rule`: φ ⊢[1] φ
- `weaken`: Γ ⊢[p] φ → q ≤ p → Γ ⊢[q] φ
- `cut_rule`: Γ ⊢[p] φ → φ ⊢[q] ψ → Γ ⊢[p*q] ψ
- `mono_rule`: (∀x, φ x ≤ ψ x) → Γ ⊢[p] φ → Γ ⊢[p] ψ

### Classical Logic Laws
- `prob_lem`: φ x + (¬ₚ φ) x = 1 (LEM as algebra)
- `prob_double_neg`: ¬ₚ (¬ₚ φ) = φ
- `lem_expectation`: E[φ|ψ] + E[¬ₚφ|ψ] = 1

### Boolean Algebra Closure
- `classical_and_closed`, `classical_or_closed`, `classical_not_closed`

## Implementation Notes

- Lean 4 v4.14.0 (see `lean/lean-toolchain`)
- Probability is axiomatized (not constructed from measure theory)
- Conditional expectation `𝔼[_|_]` is the core primitive
- Classical logic operations (`∧ₚ`, `∨ₚ`, `¬ₚ`) are `noncomputable` (depend on axiom operations)
