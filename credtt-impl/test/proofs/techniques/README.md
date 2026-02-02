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

- `01-19_*.ctt`: Classical proof techniques (19 files)
- `20-28_*.ctt`: CredTT-native techniques (9 files)

Total: 28 proof technique examples.

## Note on Files 20-28 (CredTT-Native Techniques)

Files 20-28 demonstrate CredTT-native techniques that have NO classical analogue.
These files are more CONCEPTUAL than the classical technique files:
- They explain HOW credence bounds, stability proofs, and limit theorems work
- They use `postulate` to set up scenarios rather than building proof chains
- The commentary explains why these techniques matter for verification

This is intentional: classical files (01-19) show how classical proofs map to
CredTT with credence tracking. Native files (20-28) explain new capabilities
that classical logic simply cannot express (interior stability, credence bounds,
degeneracy analysis, etc.).

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

## Note on Symbolic Credences (Issue #130)

These .ctt files use SYMBOLIC credence variables like `c`, `c1`, `c2`, `c_a`, etc.
The checker ACCEPTS these as variable names but does NOT verify symbolic
credence relationships. For example:
- `postulate p : A @ c` creates a postulate with symbolic credence "c"
- `derive q : B @ c from p by apply` works because "c" matches "c"
- The checker CANNOT verify that `c1 * c2` actually multiplies two credences

LIMITATION: Symbolic credences are treated as UNINTERPRETED strings. The
checker tracks credence equality syntactically, not algebraically. To verify
actual credence arithmetic, use concrete rational values like `1/2`, `1`, `0`.

## Executable Tests

For actual executable tests, see:
- `test/test_check.ml` - Type checker tests
- `test/test_proof.ml` - Proof checker tests (uses OCaml API, not .ctt files)
- `test/test_neighbourhood.ml` - Neighbourhood/stability tests

## Future Work

A parser for `.ctt` files is a potential future addition. See the
"Implementation Status" section in the paper for current limitations.
