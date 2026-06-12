# Release audit

A new reader clones the repo and reproduces the Lean build, the papers, the
checker binary, and the axiom ledger from one place. This records the audit and
the exact commands; run them on a clean checkout to reproduce.

## Toolchain

- Lean: `leanprover/lean4:v4.16.0` (`lean/lean-toolchain`).
- Mathlib: `v4.16.0` (`lean/lakefile.toml`, pinned by `rev`).
- 105 Lean modules under `lean/Cred/`.

## One-command build

```
make all        # lean build + part1..part7 with latexmk
make checker-test   # build the cred binary and run the CLI test suite
```

## Lean

```
cd lean && lake build
```

Result: `Build completed successfully.` Zero `sorry` and zero `admit` tactics in
`Cred` (the only matches for the strings are the English word "admits" in
comments). Verify:

```
rg -n '\bsorry\b|\badmit\b' Cred -g '*.lean'   # no tactic occurrences
```

## Axiom ledger

```
cd lean && lake env lean --run Cred/Branch/AxiomAudit.lean
```

Every audited core theorem depends only on `[propext, Classical.choice,
Quot.sound]`, with no `sorryAx`. Two results go the other way: the finite De
Morgan model `Cred.Three` is axiom-free, and `checkBool exampleTree = true` uses
`propext` only. See `docs/THEOREM_INVENTORY.md` for the full ledger and
`docs/VALUE_ALGEBRA.md` for the choice-free fragment.

## Papers

```
cd partN && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
```

All seven build clean, bibliography resolving, no undefined references:

| Paper | Pages |
|---|---|
| part1 | 12 |
| part2 | 26 |
| part3 | 11 |
| part4 | 14 |
| part5 | 17 |
| part6 | 19 |
| part7 | 13 |

## Executable checker

```
cd lean && lake build cred && ./.lake/build/bin/cred
```

Output (exit 0):

```
Cred standalone certificate checker (real-free executable).
checkBool exampleTree   = true
checkCodeNat exampleCode = true
```

The CLI accepts a certificate file: `cred check FILE` exits 0 (accepted),
1 (rejected), or 2 (malformed). `make checker-test` runs the behavioral suite
(`lean/test/checker_cli_test.sh`); all paths pass.

Platform note: on recent macOS the binary links with `-Wl,-no_data_const` (set in
`lean/lakefile.toml`) so `dyld` does not reject the `__DATA_CONST` segment. On
Linux the flag is inert.

## CI

`.github/workflows/ci.yml` runs the Lean build (with `lake exe cache get` for the
Mathlib cache), the zero-sorry gate, and the `part1..part7` paper matrix on every
push and pull request. The pipeline mirrors the local commands above.

## Summary

A clean checkout builds the formalization (zero sorry), reproduces the axiom
ledger, builds all seven papers, and runs the checker binary, all from `make all`
and `make checker-test`.
