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

Total: 28 proof technique examples matching the paper tables.

**Classical techniques (20 total):**
- `01-18_*.ctt`: Main classical techniques (18 files)
- `27_strong_induction.ctt`: Strong induction (classical technique #14)
- `28_contrapositive.ctt`: Contrapositive (classical technique #5)

**CredTT-native techniques (8 total):**
- `19-26_*.ctt`: CredTT-native techniques (8 files)

The numbering reflects development history; the paper (Table in Section 8)
provides canonical numbering 1-20 for classical and 21-28 for native techniques.

## Note on Files 19-26 (CredTT-Native Techniques)

Files 19-26 demonstrate CredTT-native techniques that have NO classical analogue.
These files are more CONCEPTUAL than the classical technique files:
- They explain HOW credence bounds, stability proofs, and limit theorems work
- They use `postulate` to set up scenarios rather than building proof chains
- The commentary explains why these techniques matter for verification

This is intentional: classical files show how classical proofs map to CredTT
with credence tracking. Native files explain new capabilities that classical
logic simply cannot express (interior stability, credence bounds, degeneracy
analysis, contractivity, proof factoring, dual proofs, limit theorems).

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
- `by ex_falso`/`exfalso`/`absurd`/`explosion`: credence becomes 1 (from 0)
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

## Parser Status (Issue #139)

A parser EXISTS at `credtt-impl/src/parser.mly` and `lexer.mll`, but:

1. The parser uses different syntax than these example files
   - Parser expects unicode brackets `〔 〕` not ASCII `[ ]`
   - Parser lacks some keywords used here (`stable`, `unstable`, `fixpoint`)

2. These `.ctt` files use a DOCUMENTATION SYNTAX designed for readability

To execute actual proofs, use the OCaml API directly (see test/test_proof.ml)
or update the parser to support the full syntax documented above.

See the "Implementation Status" section in the paper for details.
