# Cred: milestones, trusted base, and architecture

Status of the Cred foundations program. This document records what is
machine-checked, what is argued in the papers, what is trusted, and the
architecture decision for a self-hosting proof assistant.

## What is formalized

All Lean results build under `lake build` with zero `sorry`. Load-bearing
theorems are checked with `#print axioms` and depend only on
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).

Core algebra and conditioning
- Credence value algebra: negation, product conjunction, De Morgan disjunction,
  order, fixed points (`Core/Value.lean`).
- Set-valued admissible conditioning `Cond j e = {c | c ⊗ e = j}` with the
  singleton / interval / empty trichotomy (`Cond/Admissible.lean`).
- No ex falso: conditioning on credence zero is unconstrained
  (`conditioning_zero_any`).

Consequence and bridges
- LP / K3 / threshold consequence and the no-explosion results
  (`Core/Consequence.lean`, `Threshold.lean`).
- Crisp classical embedding (`Bridge/Crisp.lean`).
- The conditional-bridge no-go as an iff (`Bridge/CondBridgeIff.lean`).
- Reductio as countermodel emptiness, distinct from explosion
  (`Reductio.lean`, `CrossingOut.lean`).

Set theory and paradox
- `CredSet` graded-membership set theory, classical recovery on crisp data,
  graded separation, Quine atoms (`Set/Basic.lean`, `Set/Classical.lean`,
  `Set/Separation.lean`, `Set/Quine.lean`).
- Object-language Russell forced to one half (`Set/Russell.lean`).
- Object-facing Curry no-go (`Bridge/Curry.lean`, `Bridge/CurryObject.lean`).

Self-reference and incompleteness
- A genuine injective Goedel numbering with a decoder and a computed diagonal;
  the graded Goedel sentence pinned to one half (`Foundation/CodingNat.lean`).
- Provability tied to the real derivation calculus, `Con` proven, Goedel-I under
  local soundness, the internal Loeb arrow blocked by `curry_block`
  (`Foundation/ProvabilityDeriv.lean`).
- A standard arithmetic model with genuine inf/sup quantifiers satisfying the
  Robinson Q axioms at certainty, and `Con(Q)` (`Foundation/Arithmetic.lean`).
- Checker reflection and the stratified reflection step
  (`Reflection.lean`, `ReflectionTower.lean`).

Commitment and bootstrapping
- The toy model and the abstract `CommitmentSystem` (`ToyModel.lean`,
  `Commitment.lean`).
- The `SeededSystem` bootstrapping skeleton: `no_empty_bootstrap`,
  `SelfHosts`, the commitment-system embedding (`SeededSystem.lean`).
- The Cromwell / no-ex-falso tie and the credal-set / admissible-set tie
  (`Cromwell.lean`, `Lindley.lean`).

## Papers

- Part 1: congruence classification of the product De Morgan triplet.
- Part 2: chain-rule conditioning as a probability / many-valued-logic bridge.
- Part 3: paradox without explosion.
- Part 4: the irreducible commitment (prior, seed, supplied conditioning).
- Part 5: a didactic conceptual guide and glossary.
- Part 6: universal bootstrapping and seeded self-hosting.

## Trusted base and axiom ledger

The trusted base today is the Lean 4 kernel and Mathlib, plus the three standard
axioms above. `Branch/AxiomAudit.lean` prints, at build time, the axiom
dependency of each core theorem; that printout is the ledger. The audit finds no
choice-free fragment yet: every core result uses `Classical.choice`. Reducing
this is tracked work.

The certificate checker (`Foundation/Checker.lean`) plus its machine-checked
soundness (`Foundation/CheckerSoundness.lean`) is the smallest checkable surface:
the certificate type, the one-step rule checker, and the recursive check. The
goal is to shrink the trusted surface monotonically toward a minimal kernel.

## Architecture decision: the proof assistant

Decision: formulate inside Lean as a deep embedding (the current state), grow a
minimal substrate-independent kernel verified in Lean, then extract it to a
standalone checker; make the system host its own checker through stratified
reflection. Lean is the seed and the correctness oracle, not a permanent
dependency. A from-scratch unverified assistant is rejected.

Rationale: logical independence from any metatheory is impossible (the
Muenchhausen trilemma). The realistic goal is a minimal, auditable, self-described
trusted base (the de Bruijn criterion) that the system re-checks one stratum up
(bootstrapping, as in self-hosting compilers and Lean-in-Lean checkers). Part 6
develops this as the seed-transition-validator schema.

## Open frontier

Genuine multi-session research, tracked in the issues:
- completeness and cut elimination for the labelled calculus;
- the second-incompleteness boundary via representability;
- abstracting the value algebra and constructing it internally (off the reals);
- the minimal kernel, its self-representation, and extraction to a standalone
  checker.
