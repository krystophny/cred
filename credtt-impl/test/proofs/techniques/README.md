# Proof Techniques Examples

This directory contains **pedagogical examples** demonstrating how classical
proof techniques translate to CredTT's credence-based system.

## IMPORTANT: These are DOCUMENTATION, not executable code

The `.ctt` files in this directory use a **pseudocode notation** to illustrate
proof techniques. There is currently **no parser** that can execute these files.

They serve as:
1. Documentation of how each technique works in CredTT
2. Templates for understanding credence flow
3. Reference material for the paper (papers/credtt/credtt.tex)

## File Naming Convention

- `01-18_*.ctt`: Classical proof techniques (20 total)
- `19-26_*.ctt`: CredTT-native techniques (8 total)

## Syntax (Documentation Only)

```
postulate name : type [ credence ]     -- Assume term at credence
derive name : type [ c ] from x by y   -- Derive with credence tracking
contradict a b                         -- Force credence to 0
negate result from x                   -- Conclude negation at 1-c
stable name                            -- Assert Stable1
unstable name                          -- Assert Unstable0
fixpoint x = expr                      -- Solve credence equation
```

## Executable Tests

For actual executable tests, see:
- `test/test_check.ml` - Type checker tests
- `test/test_proof.ml` - Proof checker tests (uses OCaml API, not .ctt files)
- `test/test_neighbourhood.ml` - Neighbourhood/stability tests

## Future Work

A parser for `.ctt` files is a potential future addition. See the
"Implementation Status" section in the paper for current limitations.
