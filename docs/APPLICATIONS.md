# Applications

This document maps the Cred formalization to four concrete application areas.
For each, it states what is demonstrated (machine-checked in Lean), what is
proposed (the schema applies but no code exists yet), and where the open work
is. The bootstrap framing throughout is audit discipline, per
`docs/BOOTSTRAP_POSITIONING.md`: the `SeededSystem` schema is intentionally
elementary; the nontrivial content is the Cred-specific formal results it
audits.

---

## 1. Compiler bootstrapping and trusted builds

**Context.** A self-hosting compiler (e.g., the logos ladder: seed -> m0 ->
A1 -> ... -> logos) earns trust only if every stage transition is validated
and every hidden host-generated artifact is named. The classical problem is
that a host compiler can silently poison a binary even if the source is clean
(Thompson 1984).

**Schema mapping.** `lean/Cred/SeededSystem.lean` formalizes the abstract
skeleton. For a compiler ladder:

- `S`: the set of compiler binaries (artifacts at each stage).
- `Seed`: the initial trusted binary (e.g., a minimal seed m0, or a
  large-seed host binary accepted as an oracle).
- `T`: compile with the current stage binary.
- `V`: the per-transition validator (independent rebuild, binary comparison,
  or formal equivalence check).
- `E`: observational equivalence on compiled output.

`SelfHosts s` holds when `E s (T s)`: the compiler recompiles to an
equivalent of itself. `selfHosts_of_fixed` (formalized) covers the case where
the transition is an exact fixed point. `commitment_conservation`
(`lean/Cred/MetaBootstrap.lean`) makes explicit that moving the host binary
from an explicit seed into the "substrate" does not remove the commitment: the
pair (substrate, seed) is what is conserved.

**Concrete audit questions the schema forces:**

- Large-seed vs. minimal-seed: a large host binary is an accepted oracle, not
  a trusted base. The seed must be named explicitly.
- Host-oracle vs. trusted-machine: if the validator runs on the host, it
  inherits the host's trust assumptions. An independent validator on a
  different machine or toolchain reduces this.
- Forbidden inputs: every stage transition must be checkable for host-sourced
  artifacts (object files, libraries, linker scripts) that bypass the source
  ladder.

**Status.** The abstract schema and its coherence theorems are formalized
(zero `sorry`). The logos-specific stage manifest, per-transition validators,
and forbidden-input checks are proposed; they require a concrete `SeededSystem`
instance with the logos stages as the state space.

---

## 2. Hardware and bare-metal bootstrap

**Context.** A hardware platform (e.g., pcnoko) introduces an additional
layer: the trusted path can reach the raw-byte level, and the distinction
between host-generated artifacts, cross-toolchain artifacts, and genuine
raw-byte seeds is often implicit.

**Schema mapping.** The same `SeededSystem` applies. The key classification:

- Raw-byte seed: a bitstream or firmware image accepted as the root of trust,
  independent of any software toolchain. This is the minimal seed in the
  hardware sense.
- Cross-toolchain artifact: an artifact compiled by a different toolchain than
  the one under audit. This is an oracle, not a trusted artifact, unless the
  toolchain itself is in the ladder.
- Simulation-generated artifact: produced by a simulation of the target; trust
  depends on the simulator's own seed.

`commitment_conservation` applies here too: if the hardware platform behavior
is folded into the substrate rather than named as a seed commitment, the
commitment is not removed. `run_invariant_under_relocation` (formalized) makes
this explicit.

**Status.** The abstract schema applies directly. The pcnoko-specific raw-byte
seed tests, the explicit separation of simulation path from cross-toolchain
path, and the concrete `V` (validator per transition) are proposed. The
formalization side requires a `SeededSystem` instance with hardware artifact
types as `S`.

---

## 3. Structure-preserving numerics

**Context.** Numerical methods for physics (e.g., finite element, multi-physics
coupling) often violate algebraic laws that the exact solution satisfies:
positivity, conservation, or symmetry. The question is whether a numerical
solution is an admissible approximation, and at what threshold.

**Schema mapping.** `lean/Cred/Approx/Structure.lean` defines the shared
abstraction:

- `StructureDegree P x`: a credence-valued score for how well `x` satisfies
  structure `P`.
- `ExactPreserves P x`: score equals certainty (1).
- `PreservesAt t P x`: score is at least threshold `t`.
- `AdmissibleApprox t P x`: synonym; the numerical solution is admissible at
  level `t`.
- `crispScore`: lifts a classical (0/1) property into the credence framework,
  so existing correctness criteria embed as the boundary case.
- `Preserves Φ P`: a self-map keeps the exact-preservation class; the
  numerical scheme does not degrade a structure that held exactly.

The novel angle compared to standard a priori error analysis: instead of a
single real-valued error bound, the admissibility classification gives a graded
verdict. A method may be fully admissible for one structure (positivity,
`ExactPreserves`) and only threshold-admissible for another (energy
conservation, `PreservesAt 0.95`). Multi-physics coupling can introduce local
constraint violations that are admissible in one sub-domain and inadmissible in
another; the credence-valued score localizes this.

For multi-physics, the local-containment angle: if the violation of a
structure is contained to a sub-domain (its score is 1 on the complement), the
global coupling may still be admissible at a threshold above zero. This is the
genuinely novel framing relative to classical error analysis, which aggregates
globally.

**Cross-link.** Full documentation will live in `docs/STRUCTURE_PRESERVING_APPROX.md`
(planned; does not yet exist). The Lean module `Approx/Structure.lean` is the
source of truth until that doc is written.

**Status.** The abstract admissibility classification is formalized
(`Approx/Structure.lean`, zero `sorry`). Application to specific numerical
schemes, multi-physics coupling, and the local-containment theorems are
proposed. This is the area where the Cred framework offers a genuinely new
angle, not a restatement of classical results.

---

## 4. Theorem robustness auditing

**Context.** A formal proof system or AI-assisted theorem prover may accept a
proof that is fragile: small changes to axioms, rules, or parsing conventions
break the derivation. Auditing robustness asks whether a proof holds under
perturbations of the logical substrate.

**Schema mapping.** The certificate checker machinery applies directly:

- `checkFoundationCertificate` (`lean/Cred/Foundation/Checker.lean`): the
  decision procedure for a certificate tree. It accepts or rejects based on
  rule codes and arity.
- `CheckedFoundationProof.sound` (`lean/Cred/Foundation/CheckerSoundness.lean`):
  machine-checked soundness; acceptance implies the object-level consequence.
- `checkBool` (`lean/Cred/Foundation/CheckBool.lean`): the real-free
  computable checker. Its soundness bridge (`checkBool_true_sound`) holds
  without the reals, making it a minimal runtime trusted base.
- Stratified reflection (`lean/Cred/Reflection.lean`,
  `lean/Cred/ReflectionTower.lean`): level `n+1` verifies the level-`n`
  checker. This is not same-level self-soundness; the Lean kernel is always
  the outermost verifier.

Robustness auditing uses the negative examples to probe boundaries: a forged
or malformed header must fail (`forallElimEnvelope_bad_header_fails`,
`serialized_unknown_header_fails`). A proof system that silently accepts
malformed certificates has a larger trusted surface than claimed.

The no-ex-falso design is relevant: `labelled_no_ex_falso` and
`Kernel.no_ex_also_certificate` show that the calculus cannot derive an
unrelated positive conclusion from a contradiction. A system that does not
enforce this structurally is fragile under small rule changes.

**Status.** The certificate checker, its soundness, and the negative rejection
examples are formalized (zero `sorry`). The application to AI-assisted provers
(auditing generated proofs against the foundation certificate schema) is
proposed; it requires a translation layer from the target prover's proof
objects to `FoundationCertificateTree` instances.

---

## Summary table

| Application | Schema used | Formalized | Proposed |
|---|---|---|---|
| Compiler bootstrap (logos) | `SeededSystem`, `commitment_conservation` | Abstract schema, coherence theorems | logos stage manifest, per-transition validators, forbidden-input checks |
| Hardware bootstrap (pcnoko) | `SeededSystem`, `run_invariant_under_relocation` | Abstract schema | Raw-byte seed tests, simulation vs. cross-toolchain separation |
| Structure-preserving numerics | `Approx/Structure`, admissibility classification | Abstract admissibility (`StructureDegree`, `PreservesAt`, `crispScore`) | Scheme-specific theorems, local containment, multi-physics coupling |
| Theorem robustness auditing | Certificate checker, stratified reflection | Checker soundness, negative rejection, `no_ex_falso_certificate` | Translation from external prover proof objects |

In all four areas, the bootstrap schema is the accounting layer. The
mathematical content that gives the schema its teeth is the Cred-specific
formal development: admissible conditioning, no-ex-falso, the LP/K3 bridges,
the Curry block, and the real-free checker soundness bridge.
