# Submission plan

Candidate venues per paper and the shared artifact. These are targets, not
commitments. Each paper is self-contained and cites the Lean formalization by
exact theorem name (see `docs/THEOREM_INVENTORY.md`).

## Shared conventions

All parts share the notation macros (`\cred`, `\Cond`, `\conjc` for the product,
`\disjc` for the De Morgan dual, `\negc` for the complement) and the same toolchain
(Lean 4.16.0 + Mathlib 4.16.0). The bibliography is the single shared `cred.bib`,
deduplicated, with all citations resolving.

## Per-paper targets

- **Part 1 (congruence classification of the product De Morgan triplet).** Algebra
  and many-valued logic. Targets: Fuzzy Sets and Systems, Studia Logica, or an
  algebra-of-logic venue. The result is a clean classification theorem.

- **Part 2 (chain-rule conditioning as a probability / many-valued bridge).**
  Formal epistemology and approximate reasoning. Targets: the Review of Symbolic
  Logic, the Journal of Philosophical Logic, or the International Journal of
  Approximate Reasoning. The no-go theorem against a truth-functional conditional
  bridge is the headline.

- **Part 3 (paradox without explosion).** Nonclassical logic and foundations.
  Targets: the Journal of Philosophical Logic, the Notre Dame Journal of Formal
  Logic, or the Review of Symbolic Logic. The machine-checked solution-set and
  no-explosion results carry it.

- **Part 4 (the irreducible commitment).** Philosophy of science and Bayesian
  foundations. Targets: Synthese, Erkenntnis, or the British Journal for the
  Philosophy of Science. Positioned as synthesis with a formal core, not as a new
  statistics result.

- **Part 5 (didactic guide and glossary).** A reader entry point. Best as an arXiv
  companion to the series, or folded into a monograph; not a standalone research
  submission.

- **Part 6 (universal bootstrapping and seeded self-hosting).** Philosophy of
  computation. Targets: Minds and Machines or a philosophy-of-computer-science
  venue. The bootstrap schema is framed as audit discipline (see
  `docs/BOOTSTRAP_POSITIONING.md`), with one formal row and the rest marked
  analogy.

- **Part 7 (graded status in ordinary mathematics).** Interactive theorem proving
  and formal methods, given the `Cred/Approx/` and `Cred/Topology/` content.
  Targets: CPP (Certified Programs and Proofs) or ITP, with artifact evaluation.
  The contribution is the uniform machine-checked status vocabulary, not new
  numerics or topology.

## The Lean artifact

Archive the formalization with a Zenodo DOI pinned to the toolchain. For a CPP/ITP
submission, package it for artifact evaluation: a clean checkout builds with
`lake build` (zero `sorry`), the axiom ledger reproduces via
`Cred/Branch/AxiomAudit.lean`, the papers build with `latexmk`, and the checker
binary runs (`make checker-test`). See `docs/RELEASE_AUDIT.md`.

## Order of submission

Parts 1, 2, and 3 are the logical core and are ready first. Part 7 follows as the
formal-methods artifact paper. Parts 4 and 6 are the synthesis papers and can
follow once the core is in review. Part 5 ships with the series as the guide.
