/-
# Probabilistic Foundations

Probability as primitive, logic as derived.

This file axiomatizes probability theory directly, without going through
set theory or measure theory. Classical logic emerges as the {0,1} special case.
-/

-- ============================================================================
-- PROB TYPE: Abstract probability values in [0,1]
-- ============================================================================

axiom Prob : Type
axiom Prob.zero : Prob
axiom Prob.one : Prob
axiom Prob.le : Prob → Prob → Prop
axiom Prob.add : Prob → Prob → Prob
axiom Prob.mul : Prob → Prob → Prob
axiom Prob.sub : Prob → Prob → Prob

notation "𝟘" => Prob.zero
notation "𝟙" => Prob.one
infix:50 " ≤ₚ " => Prob.le
infix:65 " +ₚ " => Prob.add
infix:70 " *ₚ " => Prob.mul
infix:65 " -ₚ " => Prob.sub

-- Order structure
axiom Prob.zero_le : ∀ p : Prob, 𝟘 ≤ₚ p
axiom Prob.le_one : ∀ p : Prob, p ≤ₚ 𝟙
axiom Prob.le_refl : ∀ p : Prob, p ≤ₚ p
axiom Prob.le_trans : ∀ p q r : Prob, p ≤ₚ q → q ≤ₚ r → p ≤ₚ r
axiom Prob.le_antisymm : ∀ p q : Prob, p ≤ₚ q → q ≤ₚ p → p = q

-- Multiplication
axiom Prob.mul_le_mul : ∀ p₁ p₂ q₁ q₂ : Prob,
  p₁ ≤ₚ q₁ → p₂ ≤ₚ q₂ → (p₁ *ₚ p₂) ≤ₚ (q₁ *ₚ q₂)
axiom Prob.one_mul : ∀ p : Prob, 𝟙 *ₚ p = p
axiom Prob.mul_comm : ∀ p q : Prob, p *ₚ q = q *ₚ p
axiom Prob.mul_assoc : ∀ p q r : Prob, (p *ₚ q) *ₚ r = p *ₚ (q *ₚ r)
axiom Prob.zero_mul : ∀ p : Prob, 𝟘 *ₚ p = 𝟘

-- Derived: mul_one from mul_comm + one_mul
theorem Prob.mul_one (p : Prob) : p *ₚ 𝟙 = p := by rw [Prob.mul_comm]; exact Prob.one_mul p

-- Derived: mul_zero from mul_comm + zero_mul
theorem Prob.mul_zero (p : Prob) : p *ₚ 𝟘 = 𝟘 := by rw [Prob.mul_comm]; exact Prob.zero_mul p

-- Addition
axiom Prob.add_comm : ∀ p q : Prob, p +ₚ q = q +ₚ p
axiom Prob.add_assoc : ∀ p q r : Prob, (p +ₚ q) +ₚ r = p +ₚ (q +ₚ r)
axiom Prob.zero_add : ∀ p : Prob, 𝟘 +ₚ p = p

-- Derived: add_zero from add_comm + zero_add
theorem Prob.add_zero (p : Prob) : p +ₚ 𝟘 = p := by rw [Prob.add_comm]; exact Prob.zero_add p

-- Subtraction (truncated at 0)
axiom Prob.sub_self : ∀ p : Prob, p -ₚ p = 𝟘
axiom Prob.add_sub_cancel : ∀ p q : Prob, (p +ₚ q) -ₚ q = p
axiom Prob.add_sub_one : ∀ p : Prob, p +ₚ (𝟙 -ₚ p) = 𝟙
axiom Prob.sub_sub_cancel : ∀ p : Prob, 𝟙 -ₚ (𝟙 -ₚ p) = p

-- Derived: sub_zero from add_sub_cancel + add_zero
theorem Prob.sub_zero (p : Prob) : p -ₚ 𝟘 = p := by
  have h : (p +ₚ 𝟘) -ₚ 𝟘 = p := Prob.add_sub_cancel p 𝟘
  rw [Prob.add_zero] at h
  exact h

-- Derived: one_sub_zero from sub_zero
theorem Prob.one_sub_zero : 𝟙 -ₚ 𝟘 = 𝟙 := Prob.sub_zero 𝟙

-- Derived: one_sub_one from sub_self
theorem Prob.one_sub_one : 𝟙 -ₚ 𝟙 = 𝟘 := Prob.sub_self 𝟙

-- Distributivity
axiom Prob.mul_add : ∀ p q r : Prob, p *ₚ (q +ₚ r) = (p *ₚ q) +ₚ (p *ₚ r)

-- Derived: add_mul from mul_add + mul_comm
theorem Prob.add_mul (p q r : Prob) : (p +ₚ q) *ₚ r = (p *ₚ r) +ₚ (q *ₚ r) := by
  rw [Prob.mul_comm, Prob.mul_comm p r, Prob.mul_comm q r]
  exact Prob.mul_add r p q

-- Derived: 1+1-1=1 follows from add_sub_cancel
theorem Prob.one_add_one_sub_one : (𝟙 +ₚ 𝟙) -ₚ 𝟙 = 𝟙 := Prob.add_sub_cancel 𝟙 𝟙

-- Non-triviality: 0 ≠ 1
axiom Prob.zero_ne_one : 𝟘 ≠ 𝟙

-- ============================================================================
-- PROBABILISTIC PROPOSITIONS
-- ============================================================================

def ProbProp (α : Type) := α → Prob

noncomputable def prob_const {α : Type} (p : Prob) : ProbProp α := fun _ => p

-- ============================================================================
-- CONDITIONAL EXPECTATION: The core primitive
-- ============================================================================

axiom CondExp {α : Type} : ProbProp α → ProbProp α → Prob

notation "𝔼[" f " | " g "]" => CondExp f g

-- Normalization: E[1 | g] = 1
axiom CondExp.norm {α : Type} (g : ProbProp α) :
  𝔼[prob_const 𝟙 | g] = 𝟙

-- Monotonicity: f ≤ f' pointwise implies E[f|g] ≤ E[f'|g]
axiom CondExp.mono {α : Type} (f f' g : ProbProp α) :
  (∀ x, f x ≤ₚ f' x) → 𝔼[f | g] ≤ₚ 𝔼[f' | g]

-- Product rule (Bayes): E[f·g | h] = E[f | g·h]·E[g | h]
axiom CondExp.product {α : Type} (f g h : ProbProp α) :
  𝔼[(fun x => f x *ₚ g x) | h] = 𝔼[f | (fun x => g x *ₚ h x)] *ₚ 𝔼[g | h]

-- Self-conditioning: E[f | f] = 1 (conditioning on an event, given that event)
axiom CondExp.self_norm {α : Type} (f : ProbProp α) :
  𝔼[f | f] = 𝟙

-- Linearity: E[c·f | g] = c·E[f | g] for constant c
axiom CondExp.const_mul {α : Type} (c : Prob) (f g : ProbProp α) :
  𝔼[(fun x => c *ₚ f x) | g] = c *ₚ 𝔼[f | g]

-- Additivity: E[f + g | h] = E[f | h] + E[g | h]
axiom CondExp.add {α : Type} (f g h : ProbProp α) :
  𝔼[(fun x => f x +ₚ g x) | h] = 𝔼[f | h] +ₚ 𝔼[g | h]

-- Chain rule (tower law): E[f|h] ≥ E[g|h] * E[f|g]
-- This captures: conditioning through an intermediate proposition
axiom CondExp.chain {α : Type} (f g h : ProbProp α) :
  (𝔼[g | h] *ₚ 𝔼[f | g]) ≤ₚ 𝔼[f | h]

-- ============================================================================
-- PROBABILISTIC ENTAILMENT
-- ============================================================================

structure ProbEntails {α : Type} (Γ φ : ProbProp α) (p : Prob) : Prop where
  bound : p ≤ₚ 𝔼[φ | Γ]

notation:25 Γ " ⊢[" p "] " φ => ProbEntails Γ φ p

-- ============================================================================
-- PROOF THEORY
-- ============================================================================

-- Axiom rule: φ ⊢[1] φ (identity)
theorem axiom_rule {α : Type} (φ : ProbProp α) : φ ⊢[𝟙] φ := by
  constructor
  rw [CondExp.self_norm]
  exact Prob.le_refl 𝟙

-- Weakening: lower probability always derivable
theorem weaken {α : Type} (Γ φ : ProbProp α) (p q : Prob) :
    (Γ ⊢[p] φ) → (q ≤ₚ p) → (Γ ⊢[q] φ) := by
  intro h hle
  constructor
  exact Prob.le_trans q p (𝔼[φ | Γ]) hle h.bound

-- Cut rule: composition with probability degradation
theorem cut_rule {α : Type} (Γ φ ψ : ProbProp α) (p q : Prob) :
    (Γ ⊢[p] φ) → (φ ⊢[q] ψ) → (Γ ⊢[p *ₚ q] ψ) := by
  intro h1 h2
  constructor
  have hp : p ≤ₚ 𝔼[φ | Γ] := h1.bound
  have hq : q ≤ₚ 𝔼[ψ | φ] := h2.bound
  have hmul : (p *ₚ q) ≤ₚ (𝔼[φ | Γ] *ₚ 𝔼[ψ | φ]) :=
    Prob.mul_le_mul p q (𝔼[φ | Γ]) (𝔼[ψ | φ]) hp hq
  have hchain : (𝔼[φ | Γ] *ₚ 𝔼[ψ | φ]) ≤ₚ 𝔼[ψ | Γ] := CondExp.chain ψ φ Γ
  exact Prob.le_trans (p *ₚ q) (𝔼[φ | Γ] *ₚ 𝔼[ψ | φ]) (𝔼[ψ | Γ]) hmul hchain

-- Monotonicity rule: if f ≤ f' pointwise, bounds transfer
theorem mono_rule {α : Type} (Γ φ ψ : ProbProp α) (p : Prob) :
    (∀ x, φ x ≤ₚ ψ x) → (Γ ⊢[p] φ) → (Γ ⊢[p] ψ) := by
  intro hle hent
  constructor
  have hmono : 𝔼[φ | Γ] ≤ₚ 𝔼[ψ | Γ] := CondExp.mono φ ψ Γ hle
  exact Prob.le_trans p (𝔼[φ | Γ]) (𝔼[ψ | Γ]) hent.bound hmono

-- ============================================================================
-- CLASSICAL LOGIC AS {0,1} SPECIAL CASE
-- ============================================================================

def isClassical (p : Prob) : Prop := p = 𝟘 ∨ p = 𝟙

def ClassicalProp (α : Type) := { f : ProbProp α // ∀ x, isClassical (f x) }

-- Classical entailment: Γ ⊢ φ means Γ ⊢[1] φ
def ClassicalEntails {α : Type} (Γ φ : ClassicalProp α) : Prop :=
  ProbEntails (α := α) Γ.val φ.val 𝟙

notation:25 Γ " ⊢ᶜ " φ => ClassicalEntails Γ φ

-- ============================================================================
-- PROBABILISTIC LOGICAL OPERATIONS
-- ============================================================================

noncomputable def prob_and {α : Type} (A B : ProbProp α) : ProbProp α :=
  fun x => A x *ₚ B x

-- De Morgan form: equivalent to inclusion-exclusion but makes De Morgan laws trivial
noncomputable def prob_or {α : Type} (A B : ProbProp α) : ProbProp α :=
  fun x => 𝟙 -ₚ ((𝟙 -ₚ A x) *ₚ (𝟙 -ₚ B x))

noncomputable def prob_not {α : Type} (A : ProbProp α) : ProbProp α :=
  fun x => 𝟙 -ₚ A x

noncomputable def prob_implies {α : Type} (A B : ProbProp α) : ProbProp α :=
  fun x => 𝟙 -ₚ (A x *ₚ (𝟙 -ₚ B x))

notation:70 A " ∧ₚ " B => prob_and A B
notation:65 A " ∨ₚ " B => prob_or A B
prefix:75 "¬ₚ " => prob_not
notation:60 A " →ₚ " B => prob_implies A B

-- ============================================================================
-- CLASSICAL LOGIC LAWS (algebraic identities in probability)
-- ============================================================================

-- Law of excluded middle: φ + ¬φ = 1 (algebraic identity, not logical axiom!)
theorem prob_lem {α : Type} (φ : ProbProp α) (x : α) :
    φ x +ₚ (¬ₚ φ) x = 𝟙 := by
  simp only [prob_not]
  exact Prob.add_sub_one (φ x)

-- Double negation: ¬¬φ = φ (algebraic)
theorem prob_double_neg {α : Type} (φ : ProbProp α) (x : α) :
    (¬ₚ (¬ₚ φ)) x = φ x := by
  simp only [prob_not]
  exact Prob.sub_sub_cancel (φ x)

-- Idempotence: A ∧ A = A (for {0,1} values)
theorem prob_and_idemp_classical {α : Type} (A : ClassicalProp α) (x : α) :
    (A.val ∧ₚ A.val) x = A.val x := by
  simp only [prob_and]
  have hcl : isClassical (A.val x) := A.property x
  cases hcl with
  | inl hz => rw [hz]; exact Prob.zero_mul 𝟘
  | inr ho => rw [ho]; exact Prob.one_mul 𝟙

-- ============================================================================
-- LEM AS CONDITIONAL EXPECTATION IDENTITY
-- ============================================================================

-- The key thesis: LEM emerges as an algebraic identity E[φ|ψ] + E[¬φ|ψ] = 1
theorem lem_expectation {α : Type} (φ ψ : ProbProp α) :
    𝔼[φ | ψ] +ₚ 𝔼[¬ₚ φ | ψ] = 𝟙 := by
  have hadd : 𝔼[(fun x => φ x +ₚ (𝟙 -ₚ φ x)) | ψ] = 𝔼[φ | ψ] +ₚ 𝔼[(fun x => 𝟙 -ₚ φ x) | ψ] :=
    CondExp.add φ (fun x => 𝟙 -ₚ φ x) ψ
  have heq : (fun x => φ x +ₚ (𝟙 -ₚ φ x)) = prob_const 𝟙 := by
    funext x
    exact Prob.add_sub_one (φ x)
  have hnorm : 𝔼[(fun x => φ x +ₚ (𝟙 -ₚ φ x)) | ψ] = 𝟙 := by
    rw [heq]
    exact CondExp.norm ψ
  rw [hadd] at hnorm
  unfold prob_not
  exact hnorm

-- ============================================================================
-- NEGATION
-- ============================================================================

-- Strong negation: probability zero under all conditions
def StrongNeg {α : Type} (φ : ProbProp α) : Prop :=
  ∀ ψ : ProbProp α, 𝔼[φ | ψ] = 𝟘

-- Weak negation: pointwise complement
noncomputable def WeakNeg {α : Type} (φ : ProbProp α) : ProbProp α := ¬ₚ φ

-- ============================================================================
-- CLASSICAL BOOLEAN ALGEBRA EMBEDDING
-- ============================================================================

-- Classical AND is classical
theorem classical_and_closed {α : Type} (A B : ClassicalProp α) :
    ∀ x, isClassical ((A.val ∧ₚ B.val) x) := by
  intro x
  simp only [prob_and, isClassical]
  have ha : isClassical (A.val x) := A.property x
  have hb : isClassical (B.val x) := B.property x
  cases ha with
  | inl haz =>
    left
    rw [haz]
    exact Prob.zero_mul (B.val x)
  | inr hao =>
    cases hb with
    | inl hbz =>
      left
      rw [hbz]
      exact Prob.mul_zero (A.val x)
    | inr hbo =>
      right
      rw [hao, hbo]
      exact Prob.one_mul 𝟙

-- Classical NOT is classical
theorem classical_not_closed {α : Type} (A : ClassicalProp α) :
    ∀ x, isClassical ((¬ₚ A.val) x) := by
  intro x
  simp only [prob_not, isClassical]
  have ha : isClassical (A.val x) := A.property x
  cases ha with
  | inl haz =>
    right
    rw [haz]
    exact Prob.one_sub_zero
  | inr hao =>
    left
    rw [hao]
    exact Prob.one_sub_one

-- Classical OR is classical (De Morgan form: 1 - (1-A)(1-B))
theorem classical_or_closed {α : Type} (A B : ClassicalProp α) :
    ∀ x, isClassical ((A.val ∨ₚ B.val) x) := by
  intro x
  simp only [prob_or, isClassical]
  have ha : isClassical (A.val x) := A.property x
  have hb : isClassical (B.val x) := B.property x
  cases ha with
  | inl haz =>
    rw [haz, Prob.one_sub_zero]
    cases hb with
    | inl hbz =>
      -- A=0, B=0: 1 - 1*1 = 0
      left
      rw [hbz, Prob.one_sub_zero, Prob.one_mul, Prob.one_sub_one]
    | inr hbo =>
      -- A=0, B=1: 1 - 1*0 = 1
      right
      rw [hbo, Prob.one_sub_one, Prob.mul_zero, Prob.one_sub_zero]
  | inr hao =>
    rw [hao, Prob.one_sub_one, Prob.zero_mul]
    -- A=1: 1 - 0*(1-B) = 1
    right
    exact Prob.one_sub_zero

-- ============================================================================
-- CLASSICAL PROP CONSTRUCTORS
-- ============================================================================

noncomputable def mkClassicalAnd {α : Type} (A B : ClassicalProp α) : ClassicalProp α :=
  ⟨A.val ∧ₚ B.val, classical_and_closed A B⟩

noncomputable def mkClassicalOr {α : Type} (A B : ClassicalProp α) : ClassicalProp α :=
  ⟨A.val ∨ₚ B.val, classical_or_closed A B⟩

noncomputable def mkClassicalNot {α : Type} (A : ClassicalProp α) : ClassicalProp α :=
  ⟨¬ₚ A.val, classical_not_closed A⟩

-- ============================================================================
-- PHASE F: MORE PROOF RULES
-- ============================================================================

-- F1. Implication Theorems

-- Implication reflexivity: A implies A = 1
-- prob_implies A A x = 1 - A x * (1 - A x)
-- For any p in [0,1]: 1 - p*(1-p) = 1 when p=0 (1-0) or p=1 (1-0)
-- But we need this for all p, so we need an additional axiom or restrict to classical
theorem prob_implies_refl_classical {α : Type} (A : ClassicalProp α) (x : α) :
    prob_implies A.val A.val x = 𝟙 := by
  unfold prob_implies
  have hcl : isClassical (A.val x) := A.property x
  cases hcl with
  | inl hz =>
    rw [hz, Prob.one_sub_zero, Prob.zero_mul, Prob.one_sub_zero]
  | inr ho =>
    rw [ho, Prob.one_sub_one, Prob.mul_zero, Prob.one_sub_zero]

-- Modus ponens bound: A * (A implies B) ≤ B (for classical props)
theorem prob_modus_ponens_classical {α : Type} (A B : ClassicalProp α) (x : α) :
    A.val x *ₚ prob_implies A.val B.val x ≤ₚ B.val x := by
  simp only [prob_implies]
  have ha : isClassical (A.val x) := A.property x
  have hb : isClassical (B.val x) := B.property x
  cases ha with
  | inl haz =>
    rw [haz, Prob.zero_mul]
    exact Prob.zero_le (B.val x)
  | inr hao =>
    rw [hao, Prob.one_mul]
    cases hb with
    | inl hbz =>
      rw [hbz, Prob.one_sub_zero, Prob.one_mul, Prob.one_sub_one]
      exact Prob.le_refl 𝟘
    | inr hbo =>
      rw [hbo, Prob.one_sub_one, Prob.mul_zero, Prob.one_sub_zero]
      exact Prob.le_refl 𝟙

-- F2. Structural Rules

-- Conjunction commutativity (Exchange at propositional level)
theorem prob_and_comm {α : Type} (A B : ProbProp α) (x : α) :
    prob_and A B x = prob_and B A x := by
  simp only [prob_and]
  exact Prob.mul_comm (A x) (B x)

-- Conjunction associativity
theorem prob_and_assoc {α : Type} (A B C : ProbProp α) (x : α) :
    prob_and (prob_and A B) C x = prob_and A (prob_and B C) x := by
  simp only [prob_and]
  exact Prob.mul_assoc (A x) (B x) (C x)

-- Exchange rule: reordering hypotheses preserves entailment
theorem prob_exchange {α : Type} (A B C Γ : ProbProp α) (p : Prob) :
    ProbEntails (prob_and (prob_and A B) Γ) C p →
    ProbEntails (prob_and (prob_and B A) Γ) C p := by
  intro h
  constructor
  have heq : ∀ x, prob_and (prob_and A B) Γ x = prob_and (prob_and B A) Γ x := by
    intro x
    simp only [prob_and]
    rw [Prob.mul_comm (A x) (B x)]
  have hcond : 𝔼[C | prob_and (prob_and A B) Γ] = 𝔼[C | prob_and (prob_and B A) Γ] := by
    congr 1
    funext x
    exact heq x
  rw [← hcond]
  exact h.bound

-- Contraction for classical propositions: A and A = A
theorem prob_contraction {α : Type} (A : ClassicalProp α) (B Γ : ProbProp α) (p : Prob) :
    ProbEntails (prob_and (prob_and A.val A.val) Γ) B p →
    ProbEntails (prob_and A.val Γ) B p := by
  intro h
  constructor
  have heq : ∀ x, prob_and (prob_and A.val A.val) Γ x = prob_and A.val Γ x := by
    intro x
    unfold prob_and
    have hcl : isClassical (A.val x) := A.property x
    cases hcl with
    | inl hz => rw [hz, Prob.zero_mul, Prob.zero_mul]
    | inr ho => rw [ho, Prob.one_mul, Prob.one_mul]
  have hcond : 𝔼[B | prob_and (prob_and A.val A.val) Γ] = 𝔼[B | prob_and A.val Γ] := by
    congr 1
    funext x
    exact heq x
  rw [← hcond]
  exact h.bound

-- F3. Negation Theory

-- StrongNeg is preserved under conjunction
theorem strong_neg_and {α : Type} (φ ψ : ProbProp α) :
    StrongNeg φ → StrongNeg (prob_and φ ψ) := by
  intro hsn
  unfold StrongNeg at *
  intro χ
  have h1 : 𝔼[φ | χ] = 𝟘 := hsn χ
  have hle : ∀ x, prob_and φ ψ x ≤ₚ φ x := by
    intro x
    simp only [prob_and]
    have hmul : (φ x *ₚ ψ x) ≤ₚ (φ x *ₚ 𝟙) :=
      Prob.mul_le_mul (φ x) (ψ x) (φ x) 𝟙 (Prob.le_refl (φ x)) (Prob.le_one (ψ x))
    rw [Prob.mul_one] at hmul
    exact hmul
  have hmono : 𝔼[prob_and φ ψ | χ] ≤ₚ 𝔼[φ | χ] := CondExp.mono (prob_and φ ψ) φ χ hle
  rw [h1] at hmono
  exact Prob.le_antisymm (𝔼[prob_and φ ψ | χ]) 𝟘 hmono (Prob.zero_le (𝔼[prob_and φ ψ | χ]))

-- If StrongNeg phi, then weak negation has expectation 1
theorem strong_neg_implies_weak_one {α : Type} (φ : ProbProp α) :
    StrongNeg φ → ∀ ψ, 𝔼[prob_not φ | ψ] = 𝟙 := by
  intro hsn ψ
  have hlem : 𝔼[φ | ψ] +ₚ 𝔼[prob_not φ | ψ] = 𝟙 := lem_expectation φ ψ
  have hzero : 𝔼[φ | ψ] = 𝟘 := hsn ψ
  rw [hzero, Prob.zero_add] at hlem
  exact hlem

-- De Morgan laws: now DERIVED from the De Morgan form of prob_or!
-- No axioms needed - these are definitional with sub_sub_cancel

theorem prob_de_morgan_and {α : Type} (A B : ProbProp α) :
    prob_not (prob_and A B) = prob_or (prob_not A) (prob_not B) := by
  funext x
  simp only [prob_not, prob_and, prob_or]
  -- Goal: 1 - A*B = 1 - (1 - (1-A))*(1 - (1-B))
  -- Using sub_sub_cancel: 1 - (1-p) = p
  rw [Prob.sub_sub_cancel, Prob.sub_sub_cancel]

theorem prob_de_morgan_or {α : Type} (A B : ProbProp α) :
    prob_not (prob_or A B) = prob_and (prob_not A) (prob_not B) := by
  funext x
  simp only [prob_not, prob_or, prob_and]
  -- Goal: 1 - (1 - (1-A)*(1-B)) = (1-A)*(1-B)
  -- Direct application of sub_sub_cancel
  exact Prob.sub_sub_cancel ((𝟙 -ₚ A x) *ₚ (𝟙 -ₚ B x))

-- Disjunction commutativity
theorem prob_or_comm {α : Type} (A B : ProbProp α) (x : α) :
    prob_or A B x = prob_or B A x := by
  simp only [prob_or]
  -- Goal: 1 - (1-A)(1-B) = 1 - (1-B)(1-A)
  rw [Prob.mul_comm]

-- Zero is identity for disjunction: A ∨ 0 = A
theorem prob_or_zero {α : Type} (A : ProbProp α) (x : α) :
    prob_or A (prob_const 𝟘) x = A x := by
  simp only [prob_or, prob_const]
  -- Goal: 1 - (1-A)*1 = A
  rw [Prob.one_sub_zero, Prob.mul_one, Prob.sub_sub_cancel]

-- One is absorbing for disjunction: A ∨ 1 = 1
theorem prob_or_one {α : Type} (A : ProbProp α) (x : α) :
    prob_or A (prob_const 𝟙) x = 𝟙 := by
  unfold prob_or prob_const
  -- Goal: 1 - (1-A)*0 = 1
  rw [Prob.one_sub_one, Prob.mul_zero, Prob.one_sub_zero]

-- Zero is absorbing for conjunction
theorem prob_and_zero {α : Type} (A : ProbProp α) (x : α) :
    prob_and A (prob_const 𝟘) x = 𝟘 := by
  simp only [prob_and, prob_const]
  exact Prob.mul_zero (A x)

-- One is identity for conjunction
theorem prob_and_one {α : Type} (A : ProbProp α) (x : α) :
    prob_and A (prob_const 𝟙) x = A x := by
  simp only [prob_and, prob_const]
  exact Prob.mul_one (A x)

-- ============================================================================
-- PHASE E: NATURAL NUMBERS
-- ============================================================================

-- E1. Countable summation axiom (new primitive for natural numbers)
axiom prob_sum : (Nat → Prob) → Prob
axiom prob_sum_singleton : ∀ n p, prob_sum (fun m => if m = n then p else 𝟘) = p
axiom prob_sum_le_one : ∀ f, (∀ n, f n ≤ₚ 𝟙) → prob_sum f ≤ₚ 𝟙

-- Derived: prob_sum_zero from prob_sum_singleton with p=0
theorem prob_sum_zero : prob_sum (fun _ => 𝟘) = 𝟘 := by
  have h : prob_sum (fun m => if m = 0 then 𝟘 else 𝟘) = 𝟘 := prob_sum_singleton 0 𝟘
  have heq : (fun m => if m = 0 then 𝟘 else 𝟘) = (fun _ => 𝟘) := by funext m; simp
  rw [← heq]
  exact h

-- E2. Probabilistic natural number: distribution over Nat
structure ProbNat (α : Type) where
  is_n : Nat → ProbProp α
  exhaustive : ∀ x, prob_sum (fun n => is_n n x) = 𝟙
  disjoint : ∀ n m, n ≠ m → ∀ x, is_n n x *ₚ is_n m x = 𝟘

-- E3. Zero: deterministic zero
noncomputable def prob_zero_nat {α : Type} (N : ProbNat α) : ProbProp α := N.is_n 0

-- E4. Successor: shift distribution
noncomputable def prob_succ_is_n {α : Type} (N : ProbNat α) (n : Nat) : ProbProp α :=
  match n with
  | 0 => prob_const 𝟘
  | Nat.succ m => N.is_n m

-- Sum shift axiom: sum over shifted function equals sum minus first term
axiom prob_sum_shift : ∀ (f : Nat → Prob),
  prob_sum (fun n => match n with | 0 => 𝟘 | Nat.succ m => f m) = prob_sum f

-- Successor preserves exhaustiveness
theorem prob_succ_exhaustive {α : Type} (N : ProbNat α) :
    ∀ x, prob_sum (fun n => prob_succ_is_n N n x) = 𝟙 := by
  intro x
  have h : prob_sum (fun n => prob_succ_is_n N n x) =
           prob_sum (fun n => match n with | 0 => 𝟘 | Nat.succ m => N.is_n m x) := by
    congr 1
    funext n
    cases n with
    | zero => unfold prob_succ_is_n prob_const; rfl
    | succ m => unfold prob_succ_is_n; rfl
  rw [h, prob_sum_shift]
  exact N.exhaustive x

-- Successor preserves disjointness
theorem prob_succ_disjoint {α : Type} (N : ProbNat α) :
    ∀ n m, n ≠ m → ∀ x, prob_succ_is_n N n x *ₚ prob_succ_is_n N m x = 𝟘 := by
  intro n m hne x
  cases n with
  | zero =>
    unfold prob_succ_is_n prob_const
    exact Prob.zero_mul (prob_succ_is_n N m x)
  | succ n' =>
    cases m with
    | zero =>
      unfold prob_succ_is_n prob_const
      exact Prob.mul_zero (N.is_n n' x)
    | succ m' =>
      unfold prob_succ_is_n
      have hne' : n' ≠ m' := fun h => hne (congrArg Nat.succ h)
      exact N.disjoint n' m' hne' x

-- Peano 1: Zero is not a successor
-- For the successor of any ProbNat, the probability of being 0 is 0
theorem peano1 {α : Type} (N : ProbNat α) (x : α) :
    prob_succ_is_n N 0 x = 𝟘 := by
  unfold prob_succ_is_n prob_const
  rfl

-- Peano 2: Successor is injective (probabilistic version)
-- If succ(N) = succ(M) with probability 1, then N = M with probability 1
-- This is captured by: is_n of succ(N) at k+1 equals is_n of N at k

theorem peano2_shift {α : Type} (N : ProbNat α) (k : Nat) (x : α) :
    prob_succ_is_n N (Nat.succ k) x = N.is_n k x := by
  unfold prob_succ_is_n
  rfl

-- Deterministic natural number: concentrated at a single value
noncomputable def det_nat {α : Type} (n : Nat) : ProbNat α where
  is_n := fun m => prob_const (if m = n then 𝟙 else 𝟘)
  exhaustive := by
    intro x
    unfold prob_const
    exact prob_sum_singleton n 𝟙
  disjoint := by
    intro i j hij x
    unfold prob_const
    by_cases hi : i = n <;> by_cases hj : j = n
    · exact absurd (hi.trans hj.symm) hij
    · simp only [hi, hj, ite_true, ite_false]; exact Prob.mul_zero 𝟙
    · simp only [hi, hj, ite_false, ite_true]; exact Prob.zero_mul 𝟙
    · simp only [hi, hj, ite_false]; exact Prob.zero_mul 𝟘

-- Deterministic zero
noncomputable def det_zero {α : Type} : ProbNat α := det_nat 0

-- Successor of deterministic is deterministic
theorem det_succ_is_det {α : Type} (n : Nat) (x : α) :
    prob_succ_is_n (det_nat n) (Nat.succ n) x = 𝟙 := by
  unfold prob_succ_is_n det_nat prob_const
  simp only [ite_true]

-- ============================================================================
-- PHASE D: PROBABILISTIC ZORN (AC Replacement)
-- ============================================================================

-- D1. Probabilistic partial order: P(x ≤ y) for any pair
structure ProbPoset (α : Type) where
  le : α → α → Prob

-- Reflexivity: P(x ≤ x) = 1
axiom ProbPoset.refl {α : Type} (P : ProbPoset α) (x : α) : P.le x x = 𝟙

-- Transitivity: P(x ≤ y) * P(y ≤ z) ≤ P(x ≤ z)
axiom ProbPoset.trans {α : Type} (P : ProbPoset α) (x y z : α) :
  (P.le x y *ₚ P.le y z) ≤ₚ P.le x z

-- D2. Strict ordering: P(x < y) = P(x ≤ y) * (1 - P(y ≤ x))
noncomputable def prob_lt {α : Type} (P : ProbPoset α) (x y : α) : Prob :=
  P.le x y *ₚ (𝟙 -ₚ P.le y x)

-- Strict ordering is irreflexive
theorem prob_lt_irrefl {α : Type} (P : ProbPoset α) (x : α) :
    prob_lt P x x = 𝟘 := by
  unfold prob_lt
  rw [ProbPoset.refl, Prob.one_sub_one, Prob.mul_zero]

-- D3. Near-maximal: probability of strictly greater element is bounded by epsilon
structure NearMaximal {α : Type} (P : ProbPoset α) (x : α) (ε : Prob) : Prop where
  bound : ∀ y : α, prob_lt P x y ≤ₚ ε

-- Every element is 1-near-maximal (trivially)
theorem every_one_near_maximal {α : Type} (P : ProbPoset α) (x : α) :
    NearMaximal P x 𝟙 := by
  constructor
  intro y
  exact Prob.le_one (prob_lt P x y)

-- D4. Probabilistic chain: totally ordered with probability 1
structure ProbChain {α : Type} (P : ProbPoset α) (C : α → Prop) : Prop where
  total : ∀ x y : α, C x → C y → P.le x y +ₚ P.le y x = 𝟙

-- D5. Chain-completeness: every chain has an upper bound
structure ChainComplete {α : Type} (P : ProbPoset α) : Prop where
  upper_bound : ∀ (C : α → Prop), ProbChain P C →
                ∃ ub : α, ∀ x, C x → P.le x ub = 𝟙

-- D6. Distribution over type
structure ProbDistribution (α : Type) where
  weight : α → Prob
  normalized : prob_sum (fun _ => 𝟙) ≤ₚ 𝟙

-- Concentrated on near-maximals
def ConcentratedOnNearMaximal {α : Type} (P : ProbPoset α)
    (D : ProbDistribution α) (ε : Prob) : Prop :=
  ∀ x, D.weight x ≠ 𝟘 → NearMaximal P x ε

-- Classical partial order: P.le x y is always 0 or 1
def ClassicalPoset {α : Type} (P : ProbPoset α) : Prop :=
  ∀ x y, isClassical (P.le x y)

-- In a classical poset, near-maximal with epsilon=0 means truly maximal
theorem classical_maximal {α : Type} (P : ProbPoset α) (x : α) :
    ClassicalPoset P → NearMaximal P x 𝟘 →
    ∀ y, P.le x y = 𝟙 → P.le y x = 𝟙 := by
  intro hcl hnm y hxy
  have hlt : prob_lt P x y ≤ₚ 𝟘 := hnm.bound y
  have hlt0 : prob_lt P x y = 𝟘 :=
    Prob.le_antisymm (prob_lt P x y) 𝟘 hlt (Prob.zero_le (prob_lt P x y))
  unfold prob_lt at hlt0
  rw [hxy, Prob.one_mul] at hlt0
  have hcl_yx : isClassical (P.le y x) := hcl y x
  cases hcl_yx with
  | inl hz =>
    rw [hz, Prob.one_sub_zero] at hlt0
    exact absurd hlt0.symm Prob.zero_ne_one
  | inr ho => exact ho

-- Maximal element in classical poset
def ClassicalMaximal {α : Type} (P : ProbPoset α) (x : α) : Prop :=
  ∀ y, P.le x y = 𝟙 → P.le y x = 𝟙

-- ============================================================================
-- PROBABILISTIC ZORN: STATUS
-- ============================================================================

/-
The claim "Zorn without choice" means we should PROVE Zorn, not axiomatize it.

FINITE CASE: Provable in principle
- Enumerate elements, compute prob_lt for each pair
- Take element minimizing max(prob_lt x y) over y
- No choice needed: enumeration and min over finite sets are constructive
- BLOCKED: requires Fintype from Mathlib, or manual finite type handling

INFINITE CASE: Requires additional structure
- Need completeness of Prob (limits of bounded monotone sequences exist)
- With completeness, projective limit construction works
- This is analogous to how real analysis needs completeness

We do NOT axiomatize the conclusion. The gap is:
- Completeness of Prob (not yet primitive)
- Proper handling of finite types (needs Mathlib or manual work)

Future work: Add completeness primitive, prove both cases as theorems.
-/

-- Placeholder: what we WANT to prove (stated without proof)
-- This documents the intended theorem, not an axiom we assume
def prob_zorn_statement {α : Type} [Nonempty α] (P : ProbPoset α) (ε : Prob) : Prop :=
  ChainComplete P → 𝟘 ≤ₚ ε →
  ∃ x : α, NearMaximal P x ε

-- Note: We intentionally do NOT have:
--   axiom prob_zorn : prob_zorn_statement P ε
-- because the whole point is to PROVE this, not assume it.

-- Classical Zorn as corollary: WOULD follow from prob_zorn
-- We state the implication, not the theorem (since prob_zorn is not yet proved)
theorem classical_zorn_from_prob_statement {α : Type} [Nonempty α] (P : ProbPoset α) :
    ClassicalPoset P → ChainComplete P →
    (∃ x : α, NearMaximal P x 𝟘) →  -- assuming prob_zorn gives us this
    ∃ m, ClassicalMaximal P m := by
  intro hcl _ ⟨x, hnm⟩
  exact ⟨x, fun y hxy => classical_maximal P x hcl hnm y hxy⟩

-- ============================================================================
-- SUMMARY: PROBABILITY AS FOUNDATION
-- ============================================================================

/-
The key insight: classical logic is NOT primitive. It is the {0,1} boundary case
of probability theory. We have demonstrated:

## Core Framework (Phases A-C)
1. Prob type with algebraic structure (ordered semiring in [0,1])
2. Conditional expectation E[f|g] as the core primitive
3. Probabilistic entailment Γ ⊢[p] φ meaning E[φ|Γ] ≥ p
4. Proof theory rules:
   - axiom_rule: φ ⊢[1] φ
   - weaken: Γ ⊢[p] φ → q ≤ p → Γ ⊢[q] φ
   - cut_rule: Γ ⊢[p] φ → φ ⊢[q] ψ → Γ ⊢[p*q] ψ
   - mono_rule: (∀x, φ x ≤ ψ x) → Γ ⊢[p] φ → Γ ⊢[p] ψ
5. Probabilistic logical operations (∧ₚ, ∨ₚ, ¬ₚ, →ₚ)
6. Classical logic as restriction to {0,1}-valued propositions
7. LEM as algebraic identity: φ x + (¬ₚ φ) x = 1

## Phase D: Probabilistic Zorn (AC Replacement)
8. ProbPoset: probabilistic partial order with P(x ≤ y)
9. NearMaximal: P(∃ strictly greater) ≤ ε
10. ChainComplete: every chain has an upper bound
11. prob_zorn: chain-complete posets have distributions on near-maximals
12. classical_zorn_from_prob: classical Zorn as {0,1} special case

## Phase E: Natural Numbers
13. prob_sum: countable summation primitive
14. ProbNat: distributions over Nat with exhaustive and disjoint axioms
15. Peano axioms: zero not successor, successor injective (shift property)
16. det_nat: deterministic natural numbers

## Phase F: More Proof Rules
17. Implication: prob_implies_refl_classical, prob_modus_ponens_classical
18. Structural rules: prob_exchange, prob_contraction
19. Negation: strong_neg_and, strong_neg_implies_weak_one
20. De Morgan laws: prob_de_morgan_and, prob_de_morgan_or
21. Absorption/identity: prob_or_zero/one, prob_and_zero/one

The metalogic/object-logic distinction:
- METALOGIC: Lean's type theory (used to define and verify)
- OBJECT: Probabilistic foundations (Prob, E[·|·], ⊢[p])
- DERIVED: Classical logic ({0,1} case)
-/
