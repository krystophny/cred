/-
  Cred Foundation Diagonal

  Abstract diagonal lemma.  Full arithmetic coding is deferred: a
  DiagonalCoding supplies a quotation map and a self-application symbol,
  the two facts coding would discharge.  From the interface alone, every
  semantically unary context has a fixed-point sentence, and a provability
  predicate that reflects the Goedel sentence's own credence pins that
  sentence to the interior fixed point one half.
-/

import Cred.Foundation.Semantics

namespace Cred
namespace Foundation

universe u v w

open Credence

variable {Func : Type u} {Pred : Type v}

/-- "Variable 0 is not provable": the context behind the Goedel sentence. -/
def negProvContext (prov : Pred) : Formula Func Pred :=
  .neg (.atom prov [Term.var 0])

namespace Structure

variable (M : Structure Func Pred)

/-- Semantic counterpart of "at most variable 0 free". -/
def UnaryOn (φ : Formula Func Pred) : Prop :=
  ∀ env env' : M.Assignment, env 0 = env' 0 →
    M.evalFormula env φ = M.evalFormula env' φ

theorem negProvContext_unary (prov : Pred) :
    M.UnaryOn (negProvContext prov) := by
  intro env env' h
  simp [negProvContext, evalFormula, evalTermList, evalTerm, h]

/-- Coding interface: `code` quotes formulas as terms, and `selfApp` is a
    function symbol denoting the diagonalization map on quotations. -/
structure DiagonalCoding where
  code : Formula Func Pred → Term Func
  selfApp : Func
  code_closed : ∀ (φ : Formula Func Pred) (env env' : M.Assignment),
    M.evalTerm env (code φ) = M.evalTerm env' (code φ)
  selfApp_diag : ∀ (φ : Formula Func Pred) (env : M.Assignment),
    M.evalTerm env (Term.app selfApp [code φ]) =
      M.evalTerm env (code (φ.instantiate (code φ)))

namespace DiagonalCoding

variable {M}
variable (D : M.DiagonalCoding)

/-- The context with variable 0 routed through self-application. -/
def step (φ : Formula Func Pred) : Formula Func Pred :=
  φ.instantiate (Term.app D.selfApp [Term.var 0])

/-- The diagonal sentence: the step context applied to its own quotation. -/
def diagonal (φ : Formula Func Pred) : Formula Func Pred :=
  (D.step φ).instantiate (D.code (D.step φ))

theorem diagonal_eval_update (φ : Formula Func Pred) (env : M.Assignment) :
    M.evalFormula env (D.diagonal φ) =
      M.evalFormula
        (M.update (M.update env (M.evalTerm env (D.code (D.step φ))))
          (M.evalTerm env (D.code (D.diagonal φ)))) φ := by
  have h1 : M.evalFormula env (D.diagonal φ) =
      M.evalFormula (M.update env (M.evalTerm env (D.code (D.step φ))))
        (D.step φ) :=
    M.evalFormula_instantiate env (D.code (D.step φ)) (D.step φ)
  have h2 : M.evalFormula (M.update env (M.evalTerm env (D.code (D.step φ))))
        (D.step φ) =
      M.evalFormula
        (M.update (M.update env (M.evalTerm env (D.code (D.step φ))))
          (M.evalTerm (M.update env (M.evalTerm env (D.code (D.step φ))))
            (Term.app D.selfApp [Term.var 0]))) φ :=
    M.evalFormula_instantiate _ _ φ
  have h3 : M.evalTerm (M.update env (M.evalTerm env (D.code (D.step φ))))
        (Term.app D.selfApp [Term.var 0]) =
      M.evalTerm env (D.code (D.diagonal φ)) := by
    have h4 : M.evalTerm (M.update env (M.evalTerm env (D.code (D.step φ))))
          (Term.app D.selfApp [Term.var 0]) =
        M.evalTerm env (Term.app D.selfApp [D.code (D.step φ)]) := by
      simp [evalTerm, evalTermList, update]
    rw [h4]
    exact D.selfApp_diag (D.step φ) env
  rw [h1, h2, h3]

/-- Abstract diagonal lemma: the diagonal sentence evaluates exactly as the
    context applied to the quotation of the diagonal sentence itself. -/
theorem diagonal_eval (φ : Formula Func Pred) (hφ : M.UnaryOn φ)
    (env : M.Assignment) :
    M.evalFormula env (D.diagonal φ) =
      M.evalFormula env (φ.instantiate (D.code (D.diagonal φ))) := by
  rw [D.diagonal_eval_update φ env,
    M.evalFormula_instantiate env (D.code (D.diagonal φ)) φ]
  exact hφ _ _ rfl

/-- Existence form: every unary context has a semantic fixed point. -/
theorem diagonal_lemma (φ : Formula Func Pred) (hφ : M.UnaryOn φ) :
    ∃ G : Formula Func Pred, ∀ env : M.Assignment,
      M.evalFormula env G = M.evalFormula env (φ.instantiate (D.code G)) :=
  ⟨D.diagonal φ, fun env => D.diagonal_eval φ hφ env⟩

/-- Diagonal sentences of unary contexts evaluate independently of the
    assignment: they behave as sentences. -/
theorem diagonal_eval_const (φ : Formula Func Pred) (hφ : M.UnaryOn φ)
    (env env' : M.Assignment) :
    M.evalFormula env (D.diagonal φ) = M.evalFormula env' (D.diagonal φ) := by
  rw [D.diagonal_eval_update φ env, D.diagonal_eval_update φ env']
  exact hφ _ _ (D.code_closed (D.diagonal φ) env env')

/-- The Goedel sentence: the diagonal of "variable 0 is not provable". -/
def godel (prov : Pred) : Formula Func Pred :=
  D.diagonal (negProvContext prov)

theorem godel_eval (prov : Pred) (env : M.Assignment) :
    M.evalFormula env (D.godel prov) =
      ~(M.pred prov [M.evalTerm env (D.code (D.godel prov))]) := by
  have h : M.evalFormula env (D.godel prov) =
      M.evalFormula env
        ((negProvContext prov).instantiate (D.code (D.godel prov))) :=
    D.diagonal_eval (negProvContext prov) (M.negProvContext_unary prov) env
  rw [h]
  simp [negProvContext, Formula.instantiate, Formula.subst, Term.substList,
    Term.subst, Term.instSubst, evalFormula, evalTermList]

/-- If provability reflects the Goedel sentence's own credence at its code,
    that credence is the negation fixed point one half. -/
theorem godel_eval_half (prov : Pred) (env : M.Assignment)
    (hrefl : M.pred prov [M.evalTerm env (D.code (D.godel prov))] =
      M.evalFormula env (D.godel prov)) :
    M.evalFormula env (D.godel prov) = half := by
  have h := D.godel_eval prov env
  rw [hrefl] at h
  exact neg_fixed_point_unique _ h.symm

/-- Transparency: the provability predicate reports each sentence's own
    credence at its quotation.  Graded analogue of a truth predicate. -/
def Reflects (prov : Pred) : Prop :=
  ∀ (A : Formula Func Pred) (env : M.Assignment),
    M.pred prov [M.evalTerm env (D.code A)] = M.evalFormula env A

theorem godel_eval_half_of_reflects (prov : Pred) (h : D.Reflects prov)
    (env : M.Assignment) :
    M.evalFormula env (D.godel prov) = half :=
  D.godel_eval_half prov env (h (D.godel prov) env)

/-- The graded Goedel sentence sits strictly inside (0, 1). -/
theorem godel_interior (prov : Pred) (h : D.Reflects prov)
    (env : M.Assignment) :
    0 < (M.evalFormula env (D.godel prov)).val ∧
      (M.evalFormula env (D.godel prov)).val < 1 := by
  rw [D.godel_eval_half_of_reflects prov h env]
  constructor <;> norm_num [half_val]

/-- A crisp (0 or 1) provability value at the Goedel code contradicts
    reflection: the Tarski-Goedel obstruction in graded form. -/
theorem no_crisp_godel (prov : Pred) (env : M.Assignment)
    (hrefl : M.pred prov [M.evalTerm env (D.code (D.godel prov))] =
      M.evalFormula env (D.godel prov))
    (hcrisp : M.pred prov [M.evalTerm env (D.code (D.godel prov))] = 0 ∨
      M.pred prov [M.evalTerm env (D.code (D.godel prov))] = 1) :
    False := by
  rw [hrefl, D.godel_eval_half prov env hrefl] at hcrisp
  rcases hcrisp with h | h
  · have hv : (half : Credence).val = (0 : Credence).val :=
      congrArg Credence.val h
    norm_num [half_val] at hv
  · have hv : (half : Credence).val = (1 : Credence).val :=
      congrArg Credence.val h
    norm_num [half_val] at hv

/-- No transparent provability predicate takes only crisp values. -/
theorem no_crisp_reflects (prov : Pred) (h : D.Reflects prov)
    (hcrisp : ∀ xs : List M.Domain,
      M.pred prov xs = 0 ∨ M.pred prov xs = 1) :
    False :=
  D.no_crisp_godel prov (fun _ => M.witness) (h _ _) (hcrisp _)

end DiagonalCoding

end Structure

/-! ## Non-vacuity -/

/-- One-point structure with the only predicate held at half.  It witnesses
    that the coding interface and the reflection hypothesis are jointly
    satisfiable. -/
noncomputable def unitStructure : Structure Unit Unit where
  Domain := Unit
  witness := ()
  func _ _ := ()
  pred _ _ := half
  eq _ _ := 1
  all f := f ()
  ex f := f ()

noncomputable def unitCoding : unitStructure.DiagonalCoding where
  code _ := Term.var 0
  selfApp := ()
  code_closed _ _ _ := rfl
  selfApp_diag _ _ := rfl

theorem unit_godel_reflects (env : unitStructure.Assignment) :
    unitStructure.pred ()
        [unitStructure.evalTerm env (unitCoding.code (unitCoding.godel ()))] =
      unitStructure.evalFormula env (unitCoding.godel ()) := by
  rw [unitCoding.godel_eval () env]
  exact liar_fixed_point.symm

theorem unit_godel_half (env : unitStructure.Assignment) :
    unitStructure.evalFormula env (unitCoding.godel ()) = half :=
  unitCoding.godel_eval_half () env (unit_godel_reflects env)

end Foundation
end Cred
