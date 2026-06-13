/-
  Cred Foundation Induction

  Robinson Q (`arithQ.axioms`) has no induction schema, so left additive
  identity `0 + x = x` is not a consequence of Q.  This module adds the missing
  piece a foundation needs: a SOUND induction principle over the standard model
  `arithQ.natModel`.

  The statement is phrased over the object language through numeral
  instantiation.  Let `P` be a one-free-variable object formula.  If `P[0̄]`
  evaluates to certainty (base) and, for every `n`, certainty of `P[n̄]` forces
  certainty of `P[(S n)̄]` (step), then `P[n̄]` is certain for every standard
  natural `n`.  The proof reduces to `Nat.rec`: certainty over the standard
  model is a predicate on `Nat`, and base + step are exactly its `Nat.rec`
  inputs.

  HONESTY.  This is induction SOUNDNESS in the standard model `natModel`, not a
  claim that the object calculus proves the full first-order induction schema,
  and not full PA completeness.  It is a model-level lift: the recovered
  classical reasoning lives in `Nat` and is transported back to object formulas
  by `evalFormula_instantiate` and `eval_numeral`.  Higher Lean layers can build
  on it; it does not replace ZFC, PA, or Lean's kernel.
-/

import Cred.Foundation.SigmaOne

namespace Cred
namespace Foundation
namespace arithQ

open Credence

/-! ## Numeral instantiation collapses to a model-level predicate

Evaluating `P[n̄]` under any assignment equals evaluating `P` under the
assignment whose `var 0` is the standard natural `n`.  This is the bridge
between object-level numeral instantiation and a plain predicate on `Nat`. -/

/-- Evaluating the numeral instantiation `P[n̄]` equals evaluating `P` with the
    bound variable set to the standard natural `n`. -/
theorem eval_instantiate_numeral (env : natModel.Assignment) (P : ArithQFormula)
    (n : Nat) :
    natModel.evalFormula env (Formula.instantiate (numeral n) P) =
      natModel.evalFormula (Structure.update natModel env n) P := by
  rw [Structure.evalFormula_instantiate, eval_numeral]

/-! ## Induction soundness over the standard model -/

/-- Sound induction over the standard model.  For a one-free-variable object
    formula `P`:

    * base: `P[0̄]` is certain under `env`;
    * step: for every standard natural `n`, certainty of `P[n̄]` forces certainty
      of `P[(S n)̄]`;

    then `P[n̄]` is certain for every standard natural `n`.

    The conclusion is genuine numeral-instantiated object-level certainty; the
    proof recovers classical reasoning by `Nat.rec` on the model side. -/
theorem foundation_induction_sound (env : natModel.Assignment) (P : ArithQFormula)
    (base : natModel.evalFormula env (Formula.instantiate (numeral 0) P) = 1)
    (step : ∀ n : Nat,
      natModel.evalFormula env (Formula.instantiate (numeral n) P) = 1 →
        natModel.evalFormula env (Formula.instantiate (numeral (n + 1)) P) = 1) :
    ∀ n : Nat,
      natModel.evalFormula env (Formula.instantiate (numeral n) P) = 1 := by
  intro n
  induction n with
  | zero => exact base
  | succ k ih => exact step k ih

/-! ## A concrete instance

`0 + x = x` is the canonical fact that needs induction: Q proves `x + 0 = x`
(`axAddZero`) and `x + S y = S (x + y)` (`axAddSucc`) but not the symmetric
left identity, because Q lacks an induction schema.  Here it is recovered as a
model-level induction-sound certainty over every numeral. -/

/-- The object predicate `P(x) := 0 + x = x`. -/
def zeroAddPred : ArithQFormula := .equal (addT zeroT (v 0)) (v 0)

/-- `0 + x = x` holds at certainty for every numeral in the standard model,
    proved through `foundation_induction_sound`.  The base is `0 + 0 = 0`
    (`Nat.add_zero`); the step turns `0 + n = n` into `0 + (n + 1) = n + 1`
    via `Nat.add_succ`, mirroring the object-level use of `axAddSucc`. -/
theorem induction_example (env : natModel.Assignment) :
    ∀ n : Nat,
      natModel.evalFormula env (Formula.instantiate (numeral n) zeroAddPred) = 1 := by
  refine foundation_induction_sound env zeroAddPred ?base ?step
  case base =>
    rw [eval_instantiate_numeral]
    show natModel.eq (0 + (0 : Nat)) (0 : Nat) = 1
    exact natModel_eq_of_eq (Nat.add_zero 0)
  case step =>
    intro n _
    rw [eval_instantiate_numeral]
    show natModel.eq (0 + (n + 1 : Nat)) (n + 1 : Nat) = 1
    exact natModel_eq_of_eq (by rw [Nat.add_succ, Nat.zero_add])

end arithQ
end Foundation
end Cred
