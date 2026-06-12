# Value algebra: dependence inventory and constructive fragment

What in Cred depends on the hosted reals, what already works over abstract,
rational, or finite algebras, and what a fully internal construction would take.

## Three layers

1. **Abstract signature.** `Cred/Algebra.lean` fixes the `CredAlgebra` class: a
   carrier with `0`, `1`, negation, product conjunction, De Morgan disjunction,
   an order, and the thirteen laws the value space must satisfy. Results stated
   over `CredAlgebra` are independent of any particular carrier.

2. **Real-free models.** `Cred/Algebra/Finite.lean` instantiates the signature on
   `Bool` (two-element Boolean algebra) and on a three-element De Morgan model
   `Three`. `Cred/Algebra/Rational.lean` instantiates it on
   `RatUnit = {q : ℚ // 0 ≤ q ∧ q ≤ 1}`, the rational unit interval, with a
   homomorphism `toCredence` into the hosted interval. None of these need `ℝ`.

3. **Hosted reals.** `Cred/Core/Value.lean` builds `Credence` on the real unit
   interval. `Cred/Algebra/Completion.lean` bridges the rational model to the
   hosted one: the rationals are dense (`rat_dense_in_credence`) and the value
   algebra is order-complete (`value_algebra_complete`), reusing mathlib.

## Real-dependence inventory

Of 104 Lean modules, 42 mention `ℝ` and 62 are real-free.

- **Essentially real.** The value semantics and everything reading credences as
  real numbers: `Core/Value.lean`, the conditioning and copula modules
  (`Cond/`), the bridges (`Bridge/`), the congruence classification
  (`Congruence/`), the numerics examples (`Approx/`), and the real-valued
  arithmetic/analysis fragment (`Math/Reals.lean`, `Math/Metric.lean`). These use
  real arithmetic and the classical decidability of real equality.

- **Real-free.** The object-language and proof layer: `Foundation/Language.lean`,
  the checker and kernel (`Foundation/Checker.lean`, `Foundation/CheckBool.lean`,
  `Foundation/CodeChecker.lean`, `Kernel.lean`), the labelled sequent calculus
  (`Sequent.lean`), the certificate envelopes (`Foundation/Certificate.lean`,
  `Foundation/Serialization.lean`), and the finite/rational algebra models. The
  executable checker path is real-free end to end.

## The choice-free fragment

The finite De Morgan model is fully constructive. The algebra laws on `Three`
depend on no axioms at all:

- `Cred.Three.neg_neg`, `conj_comm`, `conj_assoc`, `conj_hi`, `conj_lo`,
  `neg_le_neg`, `conj_le_conj_left`: no axiom dependency.
- `Cred.Three.rank_inj`: `propext` only.

So the De Morgan-triplet structure of the value space (involutive negation,
commutative-associative product with unit and zero, antitone negation, monotone
conjunction) holds choice-free on a finite carrier. By contrast, the audited
hosted-reals theorems all use `Classical.choice` (see `Branch/AxiomAudit.lean`),
because real arithmetic and decidability of real equality pull it in. The
constructive core is the finite/rational algebra; the reals are where choice
enters.

## Internal-construction path

To construct the complete value interval inside Cred rather than borrowing
mathlib's `ℝ`, the steps are standard and ordered:

1. naturals (present: `Foundation/CodingNat.lean`, `Math/Nat.lean`);
2. integers and rationals (the rational model `RatUnit` is present);
3. an order or Cauchy completion of the rationals to the unit interval;
4. product, complement, and sup/inf on the completion;
5. quantifier semantics over the completed carrier.

Steps 1, 2, and the rational-to-hosted bridge (3-4 via mathlib) are in place
through `Algebra/Rational.lean` and `Algebra/Completion.lean`. A completion
built inside Cred without mathlib's `ℝ` is future work; the present completion
reuses mathlib's order-completeness rather than reconstructing it.

## Summary

- The value-algebra signature is carrier-independent.
- Finite (`Bool`, `Three`) and rational (`RatUnit`) models are real-free, and the
  finite De Morgan laws are choice-free.
- The hosted-reals layer is where `Classical.choice` enters, and the executable
  checker avoids it entirely.
- An internal completion replacing mathlib's `ℝ` remains future work.
