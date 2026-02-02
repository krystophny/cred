# Proof Techniques Examples

This directory contains **pedagogical examples** demonstrating how classical
proof techniques translate to CredTT's credence-based system.

## Status: EXECUTABLE

These `.ctt` files ARE executable via `credtt check <file>`. The proof checker
processes postulates, derives, fixpoints, and stability assertions.

They serve as:
1. Documentation of how each technique works in CredTT
2. Executable tests demonstrating credence propagation
3. Reference material for the paper (papers/credtt/credtt.tex)

## File Naming Convention

- `01-18_*.ctt`: Classical proof techniques (20 total)
- `19-26_*.ctt`: CredTT-native techniques (8 total)

## Syntax

```
postulate name : type @ credence       -- Assume term at credence
derive name : type @ c from x by y     -- Derive with credence tracking
contradict a b                         -- Force credence to 0
negate result from x                   -- Conclude negation at 1-c
stable name                            -- Assert Stable1
unstable name                          -- Assert Unstable0
fixpoint x = expr                      -- Solve credence equation
```

## Note on Tactics

The `by TACTIC` clause in `derive` statements is **didactic annotation**.
The checker accepts any identifier as a tactic name (algebra, substitution,
compose, apply, etc.) but does NOT verify the tactic semantically.

Credence propagation rules:
- `by negate`/`negation`/`complement`: credence becomes 1-c
- All other tactics: credence preserved

The tactic name documents the INTENDED reasoning step for human readers.
A full tactic verification system is future work (see GitHub issue #97).

## Executable Tests

For actual executable tests, see:
- `test/test_check.ml` - Type checker tests
- `test/test_proof.ml` - Proof checker tests (uses OCaml API, not .ctt files)
- `test/test_neighbourhood.ml` - Neighbourhood/stability tests

## Future Work

A parser for `.ctt` files is a potential future addition. See the
"Implementation Status" section in the paper for current limitations.
