# Theorem status taxonomy for ordinary mathematics

This document defines the five status levels used when classifying theorems
and propositions in the Cred framework. Each level has a precise meaning in
terms of credence values and admissibility, a Lean-shaped criterion, and a
pointer to the machinery that establishes it.

## Background: what a status classifies

A statement is evaluated relative to a family of admissible valuations (branches).
A valuation assigns a credence in [0,1] to each atom; a branch is one such
assignment. The status of a statement is determined by how its credence behaves
across all admissible branches.

The `Branch.Independence` module (`lean/Cred/Branch/Independence.lean`) defines
`Branch`, `Status`, and `classify`. The `Cond/Admissible.lean` module defines
the admissible set `Cond j e` for conditioning. `Threshold.lean` defines
`thresholdConsequence`. `Approx/Structure.lean` defines `StructureDegree`.

---

## Status definitions

### 1. Classical / crisp

**Meaning.** The statement evaluates to exactly 0 or exactly 1 under every
admissible valuation, and the boundary is the same in all branches: either
certain in every branch or impossible in every branch. On crisp input data
(credences drawn from {0,1}) the statement behaves classically.

**Lean criterion.** `classify φ branches = Status.certain` or
`classify φ branches = Status.impossible`, where every branch maps every
atom to a crisp value. Equivalently, `formulaCertainty` (threshold t = 1) or
`formulaPositivity` with the valuation restricted to {0,1}. The crisp embedding
`Bridge/Crisp.lean` gives `crisp_certainty_iff_classical` and
`crisp_positivity_iff_classical`.

**Example.** Excluded middle `φ ⊔ ~φ` evaluates to 1 on all crisp valuations
(formalized as `threshold_excluded_middle_iff` in `Threshold.lean`).

---

### 2. Graded / threshold

**Meaning.** The statement has credence at least t in every admissible valuation,
for some fixed threshold t in (0,1]. It need not reach 1; t measures the floor.
Certainty consequence is the t = 1 case.

**Lean criterion.** `thresholdConsequence t α premises conclusion` holds: for every
valuation v, if each premise reaches t then the conclusion reaches t. Defined in
`Threshold.lean`; structural rules (reflexivity, monotonicity, cut) are proven
there. `threshold_one_iff_certainty` ties the t = 1 case to `formulaCertainty`.
`StructureDegree P x = c` with `t ≤ c` characterizes preservation at threshold
t via `PreservesAt` in `Approx/Structure.lean`.

**Example.** The liar fixed point `c ⊗ ~c` reaches credence 0.25 at every
evaluation point; `thresholdConsequence (1/4) ...` holds for it, though
certainty does not.

---

### 3. Branch-dependent

**Meaning.** The statement is certain in at least one branch and impossible in
at least one other. It is not underdetermined (no branch places it strictly
inside (0,1)), but the admissible branches disagree on which boundary it occupies.
The truth value depends on which branch is realized.

**Lean criterion.** `classify φ branches = Status.branchDependent`. This requires
at least two branches, one with `evalCred b φ = 1` and one with
`evalCred b φ = 0`, and none with `evalCred b φ` strictly between 0 and 1.
Proven in the `Choice` example: `choice_branchDependent` in
`Branch/Independence.lean`.

**Example.** A choice-style atom (the `Choice : Formula Bool` worked example) is
certain in the `accept` branch and impossible in the `reject` branch, so
`classify Choice [accept, reject] = Status.branchDependent`.

---

### 4. Admissible / underdetermined

**Meaning.** The statement has a range of admissible credence values, none of which
is pinned to a single real by the evidence alone. There exist admissible branches
that place it at different interior values. From the conditioning side, this
corresponds to the admissible set `Cond j e` being a non-singleton interval
rather than a point.

**Lean criterion.** `classify φ branches = Status.underdetermined`: some branch
gives `evalCred b φ` strictly inside (0,1). On the conditioning side, the
trichotomy in `Cond/Admissible.lean`:
- `cond_singleton_of_pos`: evidence > 0 and joint <= evidence gives a singleton;
- `cond_zero_zero_univ`: zero evidence with zero joint gives all of [0,1];
- `cond_nonempty_iff`: `(Cond j e).Nonempty ↔ j.val ≤ e.val`.

The full set of admissible posteriors is `Cond j e`; the underdetermined case is
`Cond 0 0 = Set.univ`, where no constraint narrows the interval.

**Example.** Conditioning on zero evidence (`cred(B) = 0`): any value of
`cred(A|B)` is admissible; `conditioning_zero_any` (in `Cond/Admissible.lean`)
proves every credence satisfies the chain rule.

---

### 5. Inadmissible

**Meaning.** There is no admissible valuation or structure assignment satisfying
the stated constraints. The family of admissible branches is empty, or the
admissible set `Cond j e` is empty (no conditional credence solves the chain
rule). The statement cannot be assigned any coherent credence value.

**Lean criterion.** `classify φ branches = Status.contradictory` (the branch
family is empty), or `(Cond j e).Nonempty = False`, which by `cond_nonempty_iff`
is equivalent to `j.val > e.val`. An incoherent pair (joint exceeds evidence)
admits no Conditioning witness. Also: `StructureDegree P x = 0` with
`ExactPreserves P x` false; no admissible approximation at any positive threshold.

**Example.** `Cond 0.7 0.3` is empty: no conditional credence c satisfies
c * 0.3 = 0.7, since c <= 1 forces c * 0.3 <= 0.3 < 0.7.

---

## Summary table

| Status | Credence range | Branch condition | Key machinery |
|---|---|---|---|
| Classical/crisp | {0} or {1} uniformly | all branches agree at a boundary | `formulaCertainty`, `Bridge/Crisp.lean` |
| Graded/threshold | [t, 1] for some t > 0 | all branches at or above t | `thresholdConsequence`, `Threshold.lean` |
| Branch-dependent | {0, 1} split across branches | some certain, some impossible | `Branch.Status.branchDependent`, `Branch/Independence.lean` |
| Admissible/underdetermined | interval in [0,1] | some branch interior | `Status.underdetermined`, `Cond j e`, `Cond/Admissible.lean` |
| Inadmissible | empty (no witness) | no admissible branch or valuation | `Status.contradictory`, `cond_nonempty_iff`, `Cond/Admissible.lean` |

---

## Notes on scope

These statuses classify propositions relative to a given set of admissible
branches or a given pair (joint, evidence). They are not intrinsic to a
statement in isolation. A statement can be certain on one branch family and
underdetermined on another, depending on what valuations are admitted.

The `classify` function in `Branch/Independence.lean` implements the five-way
classification computably (given `DecidableEq` on atoms and a finite branch list).
The `Cond` trichotomy in `Cond/Admissible.lean` implements the conditioning
version for continuous credence values.

Neither `Branch/Independence.lean` nor `Approx/Structure.lean` depends on the
reals beyond the credence type. The real-free executable checker
(`Foundation/CheckBool.lean`) tracks the boundary between results that need the
real unit interval and those that do not.
