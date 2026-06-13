# Review checklist

Use this checklist before release or submission. Every item should either be answered in the papers/docs or turned into a follow-up issue.

## Reference docs

- `docs/THEOREM_INVENTORY.md`: every paper claim mapped to a Lean theorem, citation, or analogy, with the axiom ledger.
- `docs/RELEASE_AUDIT.md`: reproducible build of the Lean source, papers, checker binary, and axiom ledger.
- `docs/VALUE_ALGEBRA.md`: real-dependence inventory and the choice-free fragment.
- `docs/DEPENDENCE_POSITIONING_AUDIT.md`: copula/fuzzy/probability positioning guardrails.
- `docs/CLAIM_STATUS.md`: per-claim status ledger (Lean theorem / example / target / not claimed).
- `docs/LITERATURE_POSITIONING_MATRIX.md`: Cred vs neighbouring traditions, with anchors and overclaim risks.
- `docs/BOOTSTRAP_POSITIONING.md`: the claim hierarchy for the bootstrap schema.
- `docs/SUBMISSION.md`: per-paper venue plan.
- `docs/MILESTONES.md`: what is formalized, what is trusted, what remains.

## Positioning and claim discipline

- Are we presenting bookkeeping as a deep theorem?
- Does Part 6 clearly say that the bootstrap schema is elementary audit discipline, not the main mathematical discovery?
- Are claims marked as one of:
  - formal theorem;
  - standard theorem/coherence fact;
  - structured analogy;
  - philosophical synthesis;
  - engineering artifact claim?
- Are compiler, proof-kernel, Bayesian, AI, and biological readings guarded as analogies unless formalized?
- Does any abstract or conclusion imply that Cred solves emergence, biology, or foundations in general? If yes, revise.

## Lean/formalization

- Does every theorem-sounding paper claim have an exact Lean declaration or a standard citation?
- Are theorem names in the papers spelled exactly as in the Lean code?
- Does `lake build` pass on a clean checkout?
- Is the repo still zero `sorry`?
- Does the axiom ledger show no `sorryAx`?
- Are classical dependencies (`propext`, `Classical.choice`, `Quot.sound`) documented?
- Are any completeness results tautological because a rule imports semantic consequence directly? If so, is that scope stated clearly?

## Conditioning and logic

- Is admissible conditioning clearly external, not an object-language conditional?
- Is no-ex-falso explained as zero-evidence underdetermination, not as weakening inference rules?
- Is the LP/K3 bridge stated at the right threshold/positivity/certainty level?
- Is the truth-functional conditional no-go separated from ordinary material/residuated implication results?
- Is the Curry block stated at the correct level and not overgeneralized?

## Dependence, copulas, and fuzzy logic

- Does the text distinguish scalar value operations from proposition/event joints?
- Does it avoid saying or implying that `a ⊗ b = ab` is the general meaning of `cred(A ∧ B)`?
- Are product and min described as fixed coupling policies, not as the whole probability story?
- Does every min-copula uniqueness claim include the truth-functionality/idempotence/coplula-like-assumptions caveat?
- Does any phrase like "no intermediate copula" actually mean "no intermediate truth-functional idempotent scalar joint under the stated assumptions"?
- Does the text avoid implying that fuzzy truth values alone give probability?
- Is probability-as-logic stated as dependence-enriched logic: values plus event algebra/measure plus supplied dependence?
- Is the supplied joint identified as the probability-side dependence input?

## Foundations, self-reference, and arithmetic

- Are Russell/liar fixed-point claims scoped to the formal setting actually proved?
- Is the Goedel/provability layer separated from the full classical second-incompleteness machinery?
- Is the remaining PA-internal Sigma-1 representability frontier stated honestly?
- Are external computability/representability and object-language arithmetization kept separate?
- Is stratified reflection presented as level `n+1` validating level `n`, not same-level self-soundness?

## Foundation layers (dependence, proof theory, toy models)

- Does every new `\Lean` anchor in `singlepaper` resolve to a real declaration in the listed modules (`Cred/Dependence/{Context,Conditioning,RobustCollapse}.lean`, `Cred/ProofTheory/{Labels,Generative,Provenance,Branches}.lean`, `Cred/Examples/{FiniteWorlds,RobustConditioning,ProofProvenance,Branches,Sqrt2Branch}.lean`, `Cred/Math/{Parity,Divisibility}.lean`)?
- Are dependence contexts and interval-fiber images stated with the supplied-joint discipline, not as `⊗` standing in for a general `cred(A ∧ B)`?
- Is `Dependence/RobustCollapse.lean` consistent with the existing Kleene collapse, with no second collapse story?
- Does the generative calculus in `ProofTheory/Generative.lean` avoid a rule that imports semantic consequence as a side condition (no semantic-oracle rule)?
- Is generative-calculus soundness proved by induction on derivations, not by appeal to the target semantics?
- Is proof provenance (`ProofTheory/Provenance.lean`) kept distinct from semantic entailment, so a provenance tag never substitutes for a soundness proof?
- Are hypothetical-branch no-explosion results (`ProofTheory/Branches.lean`, `Examples/{Branches,Sqrt2Branch}.lean`) scoped to the branch construction, not overclaimed as full T+R semantics?
- Do all example modules stay under `Cred/Examples/` with no core declarations depending on them?
- Do the foundation layers add no internal conditional constructor; is conditioning still external?
- Does `lake build` stay green on these modules with zero `sorry` and zero warnings?

## Proof checker and trusted base

- Is the Lean proof trusted base separated from the runtime checker trusted base?
- Does the real-free `checkBool` path have a documented soundness bridge?
- Are parser/serializer/runtime/compiler/OS assumptions documented if a standalone checker is claimed?
- Are positive and negative checker examples included?
- Does any text imply the checker is fully independent of Lean before that is true?

## Bayesian claims

- Is fixed-model sequential=batch coherence separated from prior washout?
- Are different-prior convergence claims stated with assumptions?
- Are model comparison and prior-volume/Occam-factor claims standard and cited?
- Are flat, Jeffreys, maximum-entropy, robust, and universal priors described as minimal only relative to a substrate/model/measure?

## Bootstrapping and applications

- For every claimed bootstrap, are seed, substrate, transition, validator, and equivalence criterion named?
- Are oracle/scaffold paths separated from trusted paths?
- Is self-hosting distinguished from trust/correctness?
- For `logos`, can the stage ladder be audited without hidden host artifacts?
- For `pcnoko`, is the raw-byte path separated from simulation and cross-toolchain paths?

## External reviewer prompts

Ask each reviewer to identify one place where:

1. the prose sounds stronger than the theorem;
2. a hidden assumption is not named;
3. a structured analogy is presented too much like a result;
4. a citation is missing;
5. the checker/trusted-base story is ambiguous;
6. a copula/fuzzy/probability sentence conflates truth values with supplied dependence.