# Trusted-base shrinkage and minimal-kernel roadmap

## Current trusted surface

The trusted base today has four layers.

**Lean kernel and Mathlib.** All theorems compile under Lean `v4.16.0`
with Mathlib `v4.16.0` and zero `sorry`. The axiom inventory is
`propext`, `Classical.choice`, and `Quot.sound`. `Branch/AxiomAudit.lean`
prints the axiom dependency of each core theorem at build time; that
printout is the ledger. Every core result currently uses
`Classical.choice`; no choice-free fragment has been isolated yet.

**Certificate checker and its soundness proof.** `Foundation/Checker.lean`
defines the one-step rule checker (`applyFoundationRule`) and the
recursive driver (`checkFoundationCertificate`). The companion
`Foundation/CheckerSoundness.lean` machine-checks the end-to-end
soundness theorem: any accepted certificate yields a true
`FoundationThresholdConsequence`. These two files are the smallest
checkable surface above the Lean kernel.

**Real-free executable checker (`checkBool`).** `Foundation/CheckBool.lean`
defines `checkBool`, a `Credence`-free, computable checker. The threshold
`t : Credence` (whose carrier is `ℝ`) appears only in the result type of
the verified checker; every accept/reject decision is independent of its
value. `checkBool` mirrors `checkFoundationCertificate` case for case but
returns a bare `(premises, conclusion)` judgment with no reals.

The agreement theorem `checkJudgment_eq_map` (mutual structural induction
over the certificate tree) shows that for every `t` the real-free run
equals the verified run mapped to its judgment. From this,
`checkBool_eq_isSome` equates the Boolean verdict with the verified
checker's `isSome`, and `checkBool_true_sound` lifts a `true` verdict to
the object-level consequence. `checkBool exampleTree = true` holds by
`rfl` depending only on `propext`. The runtime trusted base for the
executable is `checkBool` itself, with no reals.

The native binary builds and runs: `lake exe cred` compiles
`Main.lean`, which calls `checkBool` and prints the verdict.
The `lakefile.toml` passes `-Wl,-no_data_const` to omit the
`__DATA_CONST` segment that newer macOS `dyld` rejects.
`./.lake/build/bin/cred` exits 0 and prints `checkBool exampleTree = true`.

**Code-level checker running on Goedel codes (`checkCode`), with the
reflective tie.** `Foundation/CodeChecker.lean` closes the arithmetic
loop. `Cred.SelfRep` (in `SelfRep.lean`) numbers every
`FoundationCertificateTree` injectively into `Nat` via `gnumTree`.
`CodeChecker` provides computable, fuel-bounded decoders (`decodeTerm`,
`decodeFormula`, `decodeTree`, ...) that invert the `Nat.pair` tagging
of each `gnum*` constructor and recover the tree from its code. The
checker `checkCode` decodes and then calls `checkBool`. The round-trip
lemmas (`decodeTerm_gnum`, `decodeTree_gnum`, ...) use a structural size
measure to bound the fuel that suffices. The core coincidence
`checkCode_gnumTree` shows that on any numbered tree with adequate fuel,
`checkCode` equals `checkBool` on that tree. Soundness follows:
`checkCode_gnumTree_sound` recovers the verified certificate and its
object-level consequence from a `true` arithmetic verdict.

`Foundation/Reflect.lean` ties the object-level acceptance predicate
`accepted` (on Goedel codes) to the real-free checker:
`reflect_accepted_checkBool` shows that `accepted t gf gp (gnumTree gf
gp tree)` holds exactly when `checkBool tree = true`, composing the
faithfulness of the numbering (`accepted_gnum_iff` from `SelfRep`) with
the agreement theorem from `CheckBool`.

**`MinimalKernel.lean` as the audit manifest.** `MinimalKernel.lean` is
not a new proof; it re-exports the checker, the certificate type, the
soundness theorem, and nothing else. Its role is to name, in one place,
what must be reviewed to audit the trusted base:
`Foundation.Structure.evalFormula`, `FoundationThresholdConsequence`,
the constructors of `FoundationProof`, `applyFoundationRule`,
`checkFoundationCertificate`, and `checkFoundationCertificate_sound`.
Nothing outside that list is trusted.

## The monotone-shrinkage goal

The goal is not logical independence from every metatheory; that is
impossible (the Muenchhausen trilemma: any justification of a base either
terminates in an unproved axiom, runs in a circle, or regresses
indefinitely). The realistic target is a minimal, auditable, self-described
trusted base that the system re-checks one stratum up, on the model of
self-hosting compilers and Lean-in-Lean checkers.

The shrinkage criterion is: each stage must strictly reduce the trusted
surface, and the reduction must be machine-checked. Progress is monotone
only if no new axioms are introduced without being recorded in the ledger.

## Stages toward a minimal kernel and a standalone checker

### Stage 0: current state (done)

- Lean kernel + Mathlib + three axioms.
- `checkFoundationCertificate` + `checkFoundationCertificate_sound` in
  `Foundation/Checker.lean` and `Foundation/CheckerSoundness.lean`.
- `checkBool` in `Foundation/CheckBool.lean`: real-free, computable,
  agreement-proved.
- `checkCode` in `Foundation/CodeChecker.lean`: runs on Goedel codes,
  agreement- and soundness-proved.
- `reflect_accepted_checkBool` in `Foundation/Reflect.lean`: reflective
  tie between the object-level acceptance predicate and the running checker.
- `MinimalKernel.lean`: named audit manifest.
- Native binary `lake exe cred` runs without reals.

### Stage 1: choice-free fragment

Isolate theorems that do not depend on `Classical.choice`. The axiom
ledger in `Branch/AxiomAudit.lean` currently shows full classical
dependence. The target is to factor the value algebra and the one-step
checker so that their correctness does not require choice.

This is tracked work, not yet done.

### Stage 2: rational value algebra

`Algebra/Rational.lean` constructs the credence algebra on the rational
unit interval, avoiding the reals entirely at the object level.
`Algebra/Completion.lean` completes it. A checker built over this algebra
would have no real-number dependency in its specification, only in the
completeness argument.

The rational algebra is in place. Wiring the checker to it as its primary
specification (rather than as a separate construction) is staged work.

### Stage 3: extracted standalone checker

The Lean code generator can emit a standalone binary from computable,
real-free definitions. `checkBool` and `checkCode` already satisfy this
constraint. The extraction step (via `Cred/Extraction.lean`) produces a
binary whose runtime behavior is the computable checker, with soundness
certified separately in Lean.

The native binary already builds and runs. The remaining work is to make
the extraction target self-describing: the binary should carry, or be
accompanied by, a machine-readable description of its own trusted base
and the axioms the soundness proof depends on.

### Stage 4: stratified reflection

`Reflection.lean` and `ReflectionTower.lean` develop the stratified
reflection step: the checker can be applied to a representation of its
own derivation, one stratum up. The reflective tie (`Reflect.lean`) is
the first link: the object-level acceptance predicate on codes coincides
with the running checker on the inductive tree.

A full reflection tower would show that the system can verify its own
checking behavior at each stratum, with the Lean kernel receding to the
role of a seed that is re-examined from outside. This is the structure
of self-hosting: the host compiler compiles itself; the host proof checker
checks its own checking rules.

### Stage 5: minimal self-described base

The final target state: a small kernel file (extending `MinimalKernel.lean`)
that lists every definition and theorem in the trusted base, proves that
the checker is sound over that list, and is itself checked by the
extracted binary on its own Goedel code. The trusted surface is then
exactly what the manifest names, re-verified one level up.

Full independence from a metatheory remains impossible. The goal is that
a careful human auditor can review the manifest and the extracted binary
in a few hours and confirm: if the Lean kernel is sound, the checker is
sound, and the checker checks itself.

## Cross-references

| Module | Role |
|---|---|
| `Foundation/Checker.lean` | One-step rule checker; `applyFoundationRule`, `checkFoundationCertificate` |
| `Foundation/CheckerSoundness.lean` | `checkFoundationCertificate_sound`; end-to-end soundness |
| `Foundation/CheckBool.lean` | `checkBool`; real-free computable checker; `checkBool_eq_isSome`, `checkBool_true_sound` |
| `Foundation/CodeChecker.lean` | `checkCode`; fuel-bounded decoders; `checkCode_gnumTree`; arithmetic soundness |
| `Foundation/Reflect.lean` | `reflect_accepted_checkBool`; reflective tie between `accepted` and `checkBool` |
| `MinimalKernel.lean` | Audit manifest; re-exports trusted names and nothing else |
| `SelfRep.lean` | Injective Goedel numbering; `gnumTree`, `accepted`, `accepted_gnum_iff` |
| `Reflection.lean`, `ReflectionTower.lean` | Stratified reflection; checker applied to its own derivation |
| `Algebra/Rational.lean`, `Algebra/Completion.lean` | Real-free value algebra; target for Stage 2 |
| `Branch/AxiomAudit.lean` | Axiom dependency ledger; printed at build time |
