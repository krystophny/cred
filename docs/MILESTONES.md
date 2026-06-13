# Cred: milestones, trusted base, and architecture

Status of the Cred foundations program. This document records what is
machine-checked, what is argued in the papers, what is trusted, and the
architecture decision for a self-hosting proof assistant.

## What is formalized

All Lean results build under `lake build` with zero `sorry`. Load-bearing
theorems are checked with `#print axioms` and depend only on
`propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).

The foundation-layer issue set #633–#645 (dependence contexts, robust collapse,
generative proof theory, proof provenance, branch semantics, finite-world and
sqrt2 examples, paper integration, architecture discipline) is implemented and
closed. Anchors are registered in `THEOREM_INVENTORY.md`.

Core algebra and conditioning
- Credence value algebra: negation, product conjunction, De Morgan disjunction,
  order, fixed points (`Core/Value.lean`).
- Set-valued admissible conditioning `Cond j e = {c | c ⊗ e = j}` with the
  singleton / interval / empty trichotomy (`Cond/Admissible.lean`).
- No ex falso: conditioning on credence zero is unconstrained
  (`conditioning_zero_any`).
- Dependence discipline: `⊗` is a scalar value operation, not a universal joint;
  probability-style reasoning supplies `J(A,B)` separately (`Valuation.lean`,
  `Cond/Copula.lean`).

Dependence contexts and robust collapse
- Dependence contexts carrying the joint exactly or as a Fréchet interval, with
  product / min / Fréchet-lower instances, the image conditional interval, threshold
  robustness, and dependence sensitivity (`Dependence/Context.lean`,
  `Dependence/Conditioning.lean`).
- Robust collapse of a conditional interval to a three-valued `RobustStatus`
  (`Dependence/RobustCollapse.lean`).
- Finite-world examples separating pointwise values and marginals from the joint
  (`Examples/FiniteWorlds.lean`, `Examples/RobustConditioning.lean`).

Proof provenance, branches, and the generative calculus
- A toy provenance proof type with `usedAssumptions`, `provenance_sound`, and the
  semantic-consequence gap (`theoremNode_uses_nothing`, `entails_but_unused`)
  (`ProofTheory/Provenance.lean`, `Examples/ProofProvenance.lean`).
- A toy branch type with `local_contradiction_no_explosion`, and the sqrt2
  number-theoretic seed: parity, divisibility, the core contradiction, and an explicit
  dependency chain (`ProofTheory/Branches.lean`, `Examples/Branches.lean`,
  `Math/Parity.lean`, `Math/Divisibility.lean`, `Examples/Sqrt2Branch.lean`).
- A generative connective calculus for the conjunction/disjunction fragment with
  `generative_sound`, removing the semantic-oracle side condition for that fragment
  (`ProofTheory/Labels.lean`, `ProofTheory/Generative.lean`).

Consequence and bridges
- LP / K3 / threshold consequence and the no-explosion results
  (`Core/Consequence.lean`, `Threshold.lean`).
- Crisp classical embedding (`Bridge/Crisp.lean`).
- The conditional-bridge no-go as an iff (`Bridge/CondBridgeIff.lean`).
- Reductio as countermodel emptiness, distinct from explosion
  (`Reductio.lean`, `CrossingOut.lean`).
- Truth-functional scalar joint boundary: under idempotence and copula-like
  assumptions, a single value-only joint is forced to min; general probability
  escapes by using event/proposition-specific joints (`Cond/Copula.lean`).

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

## Positioning and review guardrails

The bootstrap schema in Part 6 is intentionally elementary. It is not the deep
mathematical contribution by itself. Its role is audit discipline: every claimed
bootstrap must name its seed, substrate, transition, validator, and equivalence
criterion.

The nontrivial mathematical content remains the Cred-specific formal results:
admissible conditioning, no-ex-falso, LP/K3 bridges, the truth-functional
conditional no-go, the Curry block, the dependence/joint separation, provability/
reflection boundaries, and the real-free checker soundness bridge.

The probability slogan must be stated carefully: probability is not just fuzzy
truth values. It is dependence-enriched logic: graded/crisp values plus supplied
joint/dependence structure. T-norms are fixed scalar coupling policies, not the
general probabilistic joint.

See `docs/BOOTSTRAP_POSITIONING.md` for the claim hierarchy and
`docs/REVIEW_CHECKLIST.md` for the adversarial review questions.

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

The executable checker no longer needs the reals. `Foundation/CheckBool.lean`
gives `checkBool`, a `Credence`-free, computable certificate checker, and proves
it agrees with the verified checker for every threshold (`checkJudgment_eq_map`,
`checkBool_eq_isSome`), since the threshold only ever lived in the result type,
never the decision. A real-free `true` verdict still recovers the object-level
consequence (`checkBool_true_sound`), and `checkBool exampleTree = true` holds by
`rfl` depending only on `propext`. `Main.lean` runs it: `lake env lean --run
Main.lean` prints the verdict. So the runtime trusted base for the checker is the
small structural `checkBool`, with no reals; soundness stays certified in Lean.
The native binary `lake exe cred` builds and runs: linking with
`-Wl,-no_data_const` (in `lakefile.toml`) omits the `__DATA_CONST` segment that
the newer macOS `dyld` rejected, so `./.lake/build/bin/cred` prints the real-free
verdict (`checkBool exampleTree = true`, exit 0). The runtime trusted base for
the executable is the structural `checkBool`, with no reals.

The binary is a usable certificate checker, not a fixed example. `cred check
FILE` reads a single decimal Goedel code of a foundation certificate, decodes it
with the fuel-bounded `checkCode` path, and exits 0 (accepted), 1 (rejected), or
2 (malformed input); `cred check --explain FILE` prints the decoded root rule and
verdict; `cred examples` emits a bundled accepted code. The accepting verdict is
sound for any code: `checkCodeNat_sound` (from the general `checkCode_true_sound`)
proves that a `true` recovers a verified `CheckedFoundationProof` and its
threshold consequence, and under-fuel can only reject, never falsely accept. The
behavioral test suite `lean/test/checker_cli_test.sh` (target `make
checker-test`) covers the accept, reject, malformed, missing-file, and usage
paths.

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

Done since the first draft: completeness and cut admissibility for the labelled
calculus (`Completeness.lean`, `CutElim.lean`); the value algebra abstracted
(`Algebra.lean`) and constructed off the reals on the rational unit interval
(`Algebra/Rational.lean`); the minimal kernel (`MinimalKernel.lean`); the
self-representation substrate (`SelfRep.lean`); a real-free executable checker
(`CheckBool.lean`, above) that runs as a native binary; the code-level checker
that runs on the system's own Goedel codes and coincides with the verified checker
(`CodeChecker.lean`, `Reflect.lean`); the completion of the rational value algebra
to the complete hosted interval, with density and quantifier completeness reused
from mathlib (`Algebra/Completion.lean`); and the recursion-theoretic
representability of provability, a total computable decision
(`Representability.lean`).

The Sigma-1 layer is in place (`Foundation/SigmaOne.lean`): a definable order on
the Q signature with its standard-model characterization (`leF_eval_one_iff`), the
quantifier-free and Sigma-1 formula classes with crisp evaluation
(`quantifierFree_crisp`, `IsSigmaOne`), Sigma-1 completeness in the standard model
(`sigmaOne_witness_complete`), the exact representability target
(`RepresentsChecker`), and the second-incompleteness boundary pinned to the Curry
block (`no_internal_loeb_arrow`).

The classical arithmetization mechanism is now formalized end to end, off the
recursion-theoretic shelf. The brick chain: pairing (`Foundation/Pairing.lean`:
`pairGraph_represents`, `unpairGraph_represents`), sequence coding
(`Foundation/SeqCoding.lean`: nil/cons/head/tail over the `nil=0, cons=pair+1`
encoding), Goedel's beta-function for bounded sequence access
(`Foundation/Beta.lean`: `betaGraph_represents`, `betaNGraph_represents`), and the
course-of-values capstone (`Foundation/TreeRepr.lean`). `isTree` is a genuine
recursive predicate (proof-tree well-formedness over the pairing encoding);
`isTree_iff_beta` characterizes it by a Sigma-1 beta condition via Mathlib's
beta-function lemma; and `treeFormula_represents` proves an explicit object-language
Sigma-1 formula is designated in the standard model exactly when `isTree n` holds.
Object-language Sigma-1 representability of a recursively-defined predicate is
proven; the specific `checkCodeNat` instance reuses this machinery with the
checker's decode equations.

## Dependence beyond the joint: a first formalized cut

The formal core treats one dependence object: the supplied scalar joint `j`, with
the admissible conditional as the fiber of `c e = j`. Three further layers come up
repeatedly in discussion. A first formalized cut of each now exists; the work
recorded below is the honest remainder, not the whole layer.

- Credal propagation over a Fréchet family. A dependence context carries the joint
  exactly or as an interval `[max(a+b-1,0), min(a,b)]`, with the product, min, and
  Fréchet-lower joints as named instances (`Dependence/Context.lean`). The image
  conditional interval, robustness above a threshold, and dependence sensitivity are
  proven (`Dependence/Conditioning.lean`), with a worked rational case
  (`Examples/RobustConditioning.lean`). Robust collapse maps an interval to a
  three-valued `RobustStatus` (`Dependence/RobustCollapse.lean`). Formalized: the
  single context and its interval image. Remaining: full credal networks over many
  propositions.
- Proof provenance. Which assumptions a derivation actually uses is a
  dependency-graph property, distinct from semantic consequence (a theorem `B` has
  `A |= B` for every `A`, yet its proof need not use `A`). A toy provenance proof type
  tracks named assumptions, `usedAssumptions` reads off the dependency set, and
  `provenance_sound` bounds it by the available names while `checks_semantic_sound`
  recovers consequence; `theoremNode_uses_nothing` and `entails_but_unused` exhibit
  the gap (`ProofTheory/Provenance.lean`, `Examples/ProofProvenance.lean`).
  Remaining: a full provenance DAG over the foundation language.
- Counterfactual branches. Reasoning under an assumption that contradicts the ambient
  theory, `T + R` with `R` false, is a hypothetical-extension question. A toy branch
  type designates formulas through a value assignment; `local_contradiction_no_explosion`
  shows a locally contradictory branch designating both halves of a contradiction
  without designating an unrelated formula (`ProofTheory/Branches.lean`,
  `Examples/Branches.lean`). The sqrt2 seed gives a concrete number-theoretic branch:
  parity and divisibility lemmas (`Math/Parity.lean`, `Math/Divisibility.lean`) feed
  `sqrt2_core_contradiction` and an explicit dependency chain
  (`Examples/Sqrt2Branch.lean`). Remaining: `T + R` branch semantics over real theories.

The generative connective calculus is a further cut. `ProofTheory/Generative.lean`
gives a labelled `Derives` relation for the conjunction/disjunction fragment with
`generative_sound`, so designation follows from the rules without a semantic-oracle
side condition for that fragment. Remaining: quantifiers, equality, and induction in
the generative calculus, and the full real-number development.

A related open item already noted elsewhere is the four-valued (FDE) extension that
would separate "both" from "neither"; the three-valued carrier cannot.

Framing, stated once and held throughout. The joint `j = cred(A ∧ B)` is supplied
dependence data, not a value function of the marginals: `cred(A)` and `cred(B)` do
not determine it. The product `⊗` is one coupling policy (independence), `min` is
another (maximum positive dependence), and a general joint is any point of the
Fréchet interval. Fuzzy logic generalizes classical logic by grading truth values;
Cred additionally generalizes the joint, keeping it as supplied structure rather
than fixing it by a truth function. Probability is not fuzzy logic with numbers; it
is logic plus dependence, and the chain-rule fiber `c ⊗ e = j` is the interface.

## Foundations roadmap: what remains for a working basis

The kernel is a serious semantic foundation, not yet a complete basis for everyday
mathematics. The honest remaining work, in dependency order:

1. Generative proof theory: extend the connective fragment with equality
   substitution, quantifier introduction/elimination, definitions, and induction,
   with direct soundness, retiring the semantic-oracle rule of the labelled calculus.
2. Proof provenance over the real foundation language (not just the toy proof type),
   with a used-assumption DAG.
3. Branch semantics for `T + R` over genuine theories, preserving the dependency
   chain through a localized contradiction.
4. Dependence networks: credal/joint families over many propositions, beyond the
   single two-proposition context.
5. A mathematics-library seed past sqrt2: order, finite sets, and further
   number theory, then a real-number development.