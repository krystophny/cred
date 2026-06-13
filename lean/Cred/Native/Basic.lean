/-
  Cred Native: the native credence logic as a standalone object

  This module presents native Cred as a self-contained many-valued logic and
  contrasts its conditioning with the product residuum. The carrier is
  V = [0,1] (the `Credence` type), with negation ~c = 1 - c, conjunction
  c₁ ⊗ c₂ (product), disjunction c₁ ⊔ c₂ (the De Morgan dual), and primitive
  conditioning via the admissible set Cond j e = {c | c ⊗ e = j}.

  KEY CONTRAST (residuum vs fiber):
  -----------------------------------------
  The product residuum e ⇒ j is a single value: 1 when e ≤ j, else j/e. The
  Cred fiber Cond j e is the full solution set of the chain rule c ⊗ e = j.
  For positive evidence the two agree: the residuum equals j/e and Cond j e is
  the singleton {j/e}. At the impossible point e = 0, j = 0 they diverge: the
  residuum still returns one value (1), but Cond 0 0 = univ leaves the
  conditional entirely unconstrained. This divergence at e = 0 is exactly the
  non-explosion mechanism of native Cred.

  Everything here reuses lemmas from Cred.Core.Value and Cred.Cond.Admissible.
-/

import Cred.Cond.Admissible

namespace Cred

namespace Native

open Credence

/-! ## Native Cred operations, restated

These wrappers expose the native primitives under the `Native` namespace and
record their defining laws via the existing `Credence` lemmas. -/

/-- Native negation is involutive. -/
theorem nativeCred_neg_neg (c : Credence) : ~~c = c := neg_neg c

/-- Native conjunction is commutative. -/
theorem nativeCred_conj_comm (c₁ c₂ : Credence) : c₁ ⊗ c₂ = c₂ ⊗ c₁ := conj_comm c₁ c₂

/-- Native disjunction is the De Morgan dual of conjunction. -/
theorem nativeCred_de_morgan (c₁ c₂ : Credence) : ~(c₁ ⊗ c₂) = ~c₁ ⊔ ~c₂ :=
  de_morgan_conj c₁ c₂

/-- Native conjunction does not distribute over disjunction: native Cred is a
    genuinely graded logic, not a Boolean algebra. -/
theorem nativeCred_not_distrib :
    ∃ c₁ c₂ c₃ : Credence, c₁ ⊗ (c₂ ⊔ c₃) ≠ (c₁ ⊗ c₂) ⊔ (c₁ ⊗ c₃) :=
  conj_disj_not_distrib

/-! ## The product residuum

The product residuum `prodResiduum e j` is the largest c with c ⊗ e ≤ j; for
the product t-norm it is `1` when `e ≤ j` and `j/e` otherwise. We package it as
a single `Credence` value so it can be compared directly with the fiber. -/

/-- The product residuum e ⇒ j as a single credence value: 1 when e ≤ j,
    otherwise j/e. -/
noncomputable def prodResiduum (e j : Credence) : Credence :=
  if h : e.val ≤ j.val then 1
  else ⟨j.val / e.val, div_nonneg j.nonneg e.nonneg,
    by
      rcases le_or_lt e.val 0 with he | he
      · have : e.val = 0 := le_antisymm he e.nonneg
        simp [this]
      · rw [div_le_one he]; exact le_of_lt (lt_of_not_le h)⟩

/-- On the high diagonal (e ≤ j) the residuum saturates at 1. -/
theorem prodResiduum_eq_one (e j : Credence) (h : e.val ≤ j.val) :
    prodResiduum e j = 1 := by
  simp [prodResiduum, h]

/-- Below the diagonal (j < e, so in particular j ≤ e) the residuum is j/e. -/
theorem prodResiduum_val_of_lt (e j : Credence) (h : j.val < e.val) :
    (prodResiduum e j).val = j.val / e.val := by
  have hne : ¬ e.val ≤ j.val := not_le.mpr h
  simp [prodResiduum, hne]

/-- The residuum at the impossible point e = 0, j = 0 returns the single
    value 1. -/
theorem prodResiduum_zero_zero : prodResiduum 0 0 = 1 := by
  simp [prodResiduum]

/-! ## The Cred fiber

The fiber over (j, e) is the admissible set Cond j e of the chain rule. Its
shape is the source of non-explosion. -/

/-- Positive evidence makes the fiber a singleton: the unique conditional j/e.
    Restatement of `cond_singleton_of_pos`. -/
theorem nativeCred_cond_positive_singleton (j e : Credence) (he : 0 < e.val)
    (hle : j.val ≤ e.val) :
    Cond j e = {(conditioning_mk j e he hle).condCred} :=
  cond_singleton_of_pos j e he hle

/-- At the impossible point the fiber is everything: Cond 0 0 = univ.
    Restatement of `cond_zero_zero_univ`. -/
theorem nativeCred_cond_zero : Cond 0 0 = Set.univ := cond_zero_zero_univ

/-! ## Residuum versus fiber

The contrast that drives native Cred: for positive evidence the residuum and
the fiber agree (single value j/e, singleton fiber), but at e = 0, j = 0 the
residuum still returns a value while the fiber is all of [0,1]. -/

/-- For positive evidence and a coherent joint (j ≤ e), the residuum equals the
    unique fiber element, and the fiber is exactly its singleton. The residuum
    is a total function picking the one admissible conditional. -/
theorem residuum_vs_fiber_positive (j e : Credence) (he : 0 < e.val)
    (hle : j.val ≤ e.val) :
    (prodResiduum e j).val = (conditioning_mk j e he hle).condCred.val ∧
      Cond j e = {(prodResiduum e j)} := by
  have hval : (prodResiduum e j).val = j.val / e.val := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact prodResiduum_val_of_lt e j hlt
    · -- j = e with e > 0, so e ≤ j and residuum = 1 = e/e = j/e
      have hej : e.val ≤ j.val := le_of_eq heq.symm
      rw [prodResiduum_eq_one e j hej]
      simp only [one_val]
      rw [heq]; exact (div_self (ne_of_gt he)).symm
  refine ⟨hval, ?_⟩
  have hcond : (conditioning_mk j e he hle).condCred.val = j.val / e.val := rfl
  have hsing := cond_singleton_of_pos j e he hle
  rw [hsing]
  congr 1
  ext
  rw [hval, hcond]

/-- The decisive divergence at the impossible point. The residuum is a single
    value (1) while the fiber Cond 0 0 is all of [0,1]; in particular the fiber
    is not the residuum's singleton. This is the native non-explosion: zero
    evidence imposes no constraint, so no truth-functional residuum can stand
    in for conditioning there. -/
theorem residuum_vs_fiber_zero :
    prodResiduum 0 0 = 1 ∧
      Cond 0 0 = Set.univ ∧
      Cond (0 : Credence) 0 ≠ {prodResiduum 0 0} := by
  refine ⟨prodResiduum_zero_zero, cond_zero_zero_univ, ?_⟩
  rw [cond_zero_zero_univ]
  intro h
  -- univ = {1} would force every credence to equal 1; 0 ≠ 1 refutes it.
  have hmem : (0 : Credence) ∈ ({prodResiduum 0 0} : Set Credence) := by
    rw [← h]; exact Set.mem_univ 0
  rw [prodResiduum_zero_zero, Set.mem_singleton_iff] at hmem
  have : (0 : ℝ) = 1 := congrArg val hmem
  norm_num at this

end Native

end Cred
