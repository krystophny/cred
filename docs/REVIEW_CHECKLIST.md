# Review checklist

Use this checklist before release or submission. Every item should either be answered in the papers/docs or turned into a follow-up issue.

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

## Foundations, self-reference, and arithmetic

- Are Russell/liar fixed-point claims scoped to the formal setting actually proved?
- Is the Goedel/provability layer separated from the full classical second-incompleteness machinery?
- Is the remaining PA-internal Sigma-1 representability frontier stated honestly?
- Are external computability/representability and object-language arithmetization kept separate?
- Is stratified reflection presented as level `n+1` validating level `n`, not same-level self-soundness?

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
5. the checker/trusted-base story is ambiguous.
