/-
  Cred Foundation Benchmark Suite

  One module that names, in benchmark form, what the foundation layer delivers.
  Each `foundation_benchmark_*` is an alias for an already-proved result; the
  proof is the underlying theorem, so the suite adds no new trust and cannot
  drift from the source modules. `foundation_benchmark_master` bundles the load-
  bearing facts as a single conjunction.

  Scope, honest: classical PROPOSITIONAL reasoning is recovered exactly on the
  crisp fragment; threshold/certainty consequence, equality substitution, and
  quantifier elimination/introduction are sound; induction is sound in the
  standard model; the sqrt(2) descent contradicts; the second-incompleteness
  boundary holds as the absence of an internal Loeb arrow; conditioning on
  impossible evidence is unconstrained (no ex falso); and the conditioning fiber
  is a singleton/full/empty trichotomy.
-/

import Cred.Foundation.ClassicalRecovery
import Cred.Foundation.Induction
import Cred.Foundation.HigherLayerDemo
import Cred.Foundation.Equality
import Cred.Foundation.Quantifier
import Cred.Bridge.Crisp
import Cred.Cond.Admissible
import Cred.Sequent

namespace Cred.Foundation

open Cred
open Cred.Foundation.Structure
open Cred.Foundation.arithQ

universe u v w

/-! ## Classical recovery

The crisp fragment is exactly classical propositional logic, and crisp
certainty consequence is the pointwise classical relation. -/

/-- Benchmark: classical propositional logic is the crisp fragment of Cred. -/
theorem foundation_benchmark_classical_recovery {α : Type*} :
    (∀ (premises : List (Cred.Formula α)) (conclusion : Cred.Formula α),
      crispCertainty α premises conclusion ↔
      classicalConsequence α premises conclusion) ∧
    (∀ (premises : List (Cred.Formula α)) (conclusion : Cred.Formula α),
      crispCertainty α premises conclusion ↔
      (∀ v : α → Bool, (∀ p ∈ premises, classicalEval v p = true) →
        classicalEval v conclusion = true)) ∧
    (∀ (w : α → Credence), (∀ a, w a = 0 ∨ w a = 1) → ∀ A : Cred.Formula α,
      evalCred w (Cred.Formula.disj A (Cred.Formula.neg A)) = 1) ∧
    (∀ (w : α → Credence), (∀ a, w a = 0 ∨ w a = 1) → ∀ A : Cred.Formula α,
      evalCred w (Cred.Formula.conj A (Cred.Formula.neg A)) = 0) ∧
    (∀ (w : α → Credence) (A : Cred.Formula α),
      evalCred w (Cred.Formula.neg (Cred.Formula.neg A)) = evalCred w A) ∧
    (∀ A B : Cred.Formula α, crispCertainty α [A, materialImp A B] B) ∧
    (∀ A B : Cred.Formula α, crispCertainty α [A, B] (Cred.Formula.conj A B)) ∧
    (∀ A B : Cred.Formula α, crispCertainty α [Cred.Formula.conj A B] A) ∧
    (∀ A B : Cred.Formula α, crispCertainty α [Cred.Formula.conj A B] B) ∧
    (∀ A B : Cred.Formula α, crispCertainty α [A] (Cred.Formula.disj A B)) ∧
    (∀ A B : Cred.Formula α, crispCertainty α [B] (Cred.Formula.disj A B)) :=
  classical_propositional_is_fragment

/-- Benchmark: on crisp valuations, certainty consequence is classical
    consequence. -/
theorem foundation_benchmark_crisp_certainty_classical (α : Type*)
    (premises : List (Cred.Formula α)) (conclusion : Cred.Formula α) :
    crispCertainty α premises conclusion ↔
    classicalConsequence α premises conclusion :=
  crisp_certainty_iff_classical α premises conclusion

/-! ## Consequence soundness

The first-order threshold and certainty consequence relations satisfy the
structural rules, and the foundation proof calculus is sound for them. -/

/-- Benchmark: threshold-consequence reflexivity. -/
theorem foundation_benchmark_threshold_refl {Func : Type u} {Pred : Type v}
    (t : Credence) (φ : Formula Func Pred) :
    Structure.ThresholdConsequence.{u, v, w} t [φ] φ :=
  Structure.threshold_reflexivity t φ

/-- Benchmark: threshold-consequence cut. -/
theorem foundation_benchmark_threshold_cut {Func : Type u} {Pred : Type v}
    (t : Credence) {Γ : List (Formula Func Pred)} {φ ψ : Formula Func Pred}
    (h1 : Structure.ThresholdConsequence.{u, v, w} t Γ φ)
    (h2 : Structure.ThresholdConsequence.{u, v, w} t (φ :: Γ) ψ) :
    Structure.ThresholdConsequence.{u, v, w} t Γ ψ :=
  Structure.threshold_cut t h1 h2

/-- Benchmark: certainty-consequence reflexivity. -/
theorem foundation_benchmark_certainty_refl {Func : Type u} {Pred : Type v}
    (φ : Formula Func Pred) :
    Structure.CertaintyConsequence.{u, v, w} [φ] φ :=
  Structure.certainty_reflexivity φ

/-- Benchmark: soundness of the combined foundation proof calculus. -/
theorem foundation_benchmark_calculus_sound {Func : Type u} {Pred : Type v}
    {t : Credence} {Γ : List (Formula Func Pred)} {φ : Formula Func Pred}
    (h : Structure.FoundationDerivation t Γ φ) :
    Structure.FoundationThresholdConsequence.{u, v, w} t Γ φ :=
  Structure.foundation_derivation_sound h

/-! ## Equality and quantifiers

Equality substitution and the quantifier elimination/introduction laws hold as
crisp/quantifier threshold consequences, and their derivation calculi are
sound. -/

/-- Benchmark: equality substitution as a crisp threshold consequence. -/
theorem foundation_benchmark_equality_subst {Func : Type u} {Pred : Type v}
    (t : Credence) (τ υ : Term Func) (φ : Formula Func Pred) :
    Structure.CrispThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred τ υ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) :=
  Structure.equality_substitution_threshold t τ υ φ

/-- Benchmark: soundness of the crisp-equality derivation calculus. -/
theorem foundation_benchmark_crisp_derivation_sound {Func : Type u}
    {Pred : Type v} {t : Credence} {Γ : List (Formula Func Pred)}
    {φ : Formula Func Pred} (h : Structure.CrispDerivation t Γ φ) :
    Structure.CrispThresholdConsequence.{u, v, w} t Γ φ :=
  Structure.crisp_derivation_sound h

/-- Benchmark: universal elimination as a quantifier threshold consequence. -/
theorem foundation_benchmark_forall_elim {Func : Type u} {Pred : Type v}
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    Structure.QuantifierThresholdConsequence.{u, v, w} t
      [.forallE φ] (Formula.instantiate τ φ) :=
  Structure.forall_elim_formula t φ τ

/-- Benchmark: existential introduction as a quantifier threshold consequence. -/
theorem foundation_benchmark_exists_intro {Func : Type u} {Pred : Type v}
    (t : Credence) (φ : Formula Func Pred) (τ : Term Func) :
    Structure.QuantifierThresholdConsequence.{u, v, w} t
      [Formula.instantiate τ φ] (.existsE φ) :=
  Structure.exists_intro_formula t φ τ

/-- Benchmark: soundness of the quantifier derivation calculus. -/
theorem foundation_benchmark_quantifier_derivation_sound {Func : Type u}
    {Pred : Type v} {t : Credence} {Γ : List (Formula Func Pred)}
    {φ : Formula Func Pred} (h : Structure.QuantifierDerivation t Γ φ) :
    Structure.QuantifierThresholdConsequence.{u, v, w} t Γ φ :=
  Structure.quantifier_derivation_sound h

/-! ## Induction soundness

Induction is sound in the standard model `natModel`: numeral-instantiated base
plus step force certainty at every standard natural. -/

/-- Benchmark: sound induction over the standard arithmetic model. -/
theorem foundation_benchmark_induction_sound (env : natModel.Assignment)
    (P : ArithQFormula)
    (base : natModel.evalFormula env (Formula.instantiate (numeral 0) P) = 1)
    (step : ∀ n : Nat,
      natModel.evalFormula env (Formula.instantiate (numeral n) P) = 1 →
        natModel.evalFormula env (Formula.instantiate (numeral (n + 1)) P) = 1) :
    ∀ n : Nat,
      natModel.evalFormula env (Formula.instantiate (numeral n) P) = 1 :=
  foundation_induction_sound env P base step

/-! ## Arithmetic benchmark

The sqrt(2) descent has no coprime witness. -/

/-- Benchmark: the sqrt(2) irrationality core contradiction. -/
theorem foundation_benchmark_sqrt2_contradiction (p q : ℕ)
    (hco : Nat.Coprime p q) (h : p * p = 2 * (q * q)) (hq : q ≠ 0) : False :=
  Cred.Examples.Sqrt2Branch.sqrt2_core_contradiction p q hco h hq

/-! ## Provability boundary

No total internal conditional carries modus ponens, conditional proof, and
contraction together; the second-incompleteness boundary has no internal Loeb
arrow in Cred. -/

/-- Benchmark: no internal Loeb arrow (Goedel/provability boundary). -/
theorem foundation_benchmark_no_internal_loeb_arrow :
    ¬ ∃ f : Credence → Credence → Credence,
        Credence.MP f ∧ Credence.CP f ∧ Credence.Contraction f :=
  no_internal_loeb_arrow

/-! ## No explosion and the conditioning trichotomy

Conditioning on impossible evidence imposes no constraint, the labelled calculus
has no ex-falso derivation, and the conditioning fiber is singleton (positive
evidence), full (zero/zero), or empty (incoherent). -/

/-- Benchmark: zero evidence with zero joint admits every conditional, so there
    is no explosion from impossible evidence. -/
theorem foundation_benchmark_no_ex_falso_cond :
    Credence.Cond 0 0 = Set.univ :=
  Credence.cond_zero_zero_univ

/-- Benchmark: the labelled calculus derives no unrelated positive conclusion
    from `A` and `~A`. -/
theorem foundation_benchmark_labelled_no_ex_falso :
    ¬ Cred.Derivation noExFalsoContext { kind := .positive, formula := .atom 1 } :=
  labelled_no_ex_falso

/-- Benchmark: positive evidence pins a unique conditional value (singleton arm
    of the trichotomy). -/
theorem foundation_benchmark_cond_singleton (j e : Credence) (he : 0 < e.val)
    (hle : j.val ≤ e.val) :
    Credence.Cond j e = {(Credence.conditioning_mk j e he hle).condCred} :=
  Credence.cond_singleton_of_pos j e he hle

/-- Benchmark: the conditioning fiber is nonempty exactly when joint ≤ evidence
    (the empty arm of the trichotomy is its complement). -/
theorem foundation_benchmark_cond_nonempty_iff (j e : Credence) :
    (Credence.Cond j e).Nonempty ↔ j.val ≤ e.val :=
  Credence.cond_nonempty_iff j e

/-! ## Higher-layer composition

A higher Lean development derives new classical consequences purely by composing
foundation rules. -/

/-- Benchmark: a higher layer builds a derived classical consequence by composing
    foundation kernel rules. -/
theorem foundation_benchmark_higher_layer {Func : Type u} {Pred : Type v}
    (t : Credence) (τ υ : Term Func) (φ : Formula Func Pred) :
    Structure.FoundationThresholdConsequence.{u, v, w} t
      [@Formula.equal Func Pred υ τ, Formula.instantiate τ φ]
      (Formula.instantiate υ φ) :=
  Demo.higher_layer_builds_on_foundation t τ υ φ

/-! ## Master bundle

`foundation_benchmark_master` records the load-bearing benchmarks in one
conjunction: classical recovery, threshold/equality/quantifier soundness,
induction soundness, the sqrt(2) contradiction, the provability boundary, no ex
falso, and the conditioning trichotomy. -/

/-- The aggregated foundation benchmark. Each conjunct is one of the named
    `foundation_benchmark_*` anchors. -/
theorem foundation_benchmark_master :
    -- classical propositional logic is the crisp fragment
    (∀ {α : Type}, ∀ (premises : List (Cred.Formula α)) (conclusion : Cred.Formula α),
      crispCertainty α premises conclusion ↔
      classicalConsequence α premises conclusion) ∧
    -- threshold-consequence reflexivity
    (∀ (t : Credence) (φ : Formula Nat Nat),
      Structure.ThresholdConsequence.{0, 0, 0} t [φ] φ) ∧
    -- equality substitution is sound
    (∀ (t : Credence) (τ υ : Term Nat) (φ : Formula Nat Nat),
      Structure.CrispThresholdConsequence.{0, 0, 0} t
        [@Formula.equal Nat Nat τ υ, Formula.instantiate τ φ]
        (Formula.instantiate υ φ)) ∧
    -- universal elimination and existential introduction are sound
    (∀ (t : Credence) (φ : Formula Nat Nat) (τ : Term Nat),
      Structure.QuantifierThresholdConsequence.{0, 0, 0} t
        [.forallE φ] (Formula.instantiate τ φ)) ∧
    (∀ (t : Credence) (φ : Formula Nat Nat) (τ : Term Nat),
      Structure.QuantifierThresholdConsequence.{0, 0, 0} t
        [Formula.instantiate τ φ] (.existsE φ)) ∧
    -- induction is sound in the standard model
    (∀ (env : natModel.Assignment) (P : ArithQFormula),
      natModel.evalFormula env (Formula.instantiate (numeral 0) P) = 1 →
      (∀ n : Nat,
        natModel.evalFormula env (Formula.instantiate (numeral n) P) = 1 →
          natModel.evalFormula env
            (Formula.instantiate (numeral (n + 1)) P) = 1) →
      ∀ n : Nat,
        natModel.evalFormula env (Formula.instantiate (numeral n) P) = 1) ∧
    -- the sqrt(2) descent contradicts
    (∀ (p q : ℕ), Nat.Coprime p q → p * p = 2 * (q * q) → q ≠ 0 → False) ∧
    -- the provability boundary: no internal Loeb arrow
    (¬ ∃ f : Credence → Credence → Credence,
        Credence.MP f ∧ Credence.CP f ∧ Credence.Contraction f) ∧
    -- no explosion from impossible evidence
    (Credence.Cond 0 0 = Set.univ) ∧
    -- the conditioning trichotomy: nonempty exactly when joint ≤ evidence
    (∀ (j e : Credence), (Credence.Cond j e).Nonempty ↔ j.val ≤ e.val) :=
  ⟨fun {α} => foundation_benchmark_crisp_certainty_classical α,
   fun t φ => foundation_benchmark_threshold_refl t φ,
   fun t τ υ φ => foundation_benchmark_equality_subst t τ υ φ,
   fun t φ τ => foundation_benchmark_forall_elim t φ τ,
   fun t φ τ => foundation_benchmark_exists_intro t φ τ,
   fun env P base step => foundation_benchmark_induction_sound env P base step,
   fun p q hco h hq => foundation_benchmark_sqrt2_contradiction p q hco h hq,
   foundation_benchmark_no_internal_loeb_arrow,
   foundation_benchmark_no_ex_falso_cond,
   fun j e => foundation_benchmark_cond_nonempty_iff j e⟩

end Cred.Foundation
