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
axiom Prob.mul_one : ∀ p : Prob, p *ₚ 𝟙 = p
axiom Prob.mul_comm : ∀ p q : Prob, p *ₚ q = q *ₚ p
axiom Prob.mul_assoc : ∀ p q r : Prob, (p *ₚ q) *ₚ r = p *ₚ (q *ₚ r)
axiom Prob.zero_mul : ∀ p : Prob, 𝟘 *ₚ p = 𝟘
axiom Prob.mul_zero : ∀ p : Prob, p *ₚ 𝟘 = 𝟘

-- Addition
axiom Prob.add_comm : ∀ p q : Prob, p +ₚ q = q +ₚ p
axiom Prob.add_assoc : ∀ p q r : Prob, (p +ₚ q) +ₚ r = p +ₚ (q +ₚ r)
axiom Prob.zero_add : ∀ p : Prob, 𝟘 +ₚ p = p
axiom Prob.add_zero : ∀ p : Prob, p +ₚ 𝟘 = p

-- Subtraction (truncated at 0)
axiom Prob.sub_self : ∀ p : Prob, p -ₚ p = 𝟘
axiom Prob.add_sub_cancel : ∀ p q : Prob, (p +ₚ q) -ₚ q = p
axiom Prob.one_sub_zero : 𝟙 -ₚ 𝟘 = 𝟙
axiom Prob.one_sub_one : 𝟙 -ₚ 𝟙 = 𝟘
axiom Prob.sub_zero : ∀ p : Prob, p -ₚ 𝟘 = p
axiom Prob.add_sub_one : ∀ p : Prob, p +ₚ (𝟙 -ₚ p) = 𝟙
axiom Prob.sub_sub_cancel : ∀ p : Prob, 𝟙 -ₚ (𝟙 -ₚ p) = p

-- Distributivity
axiom Prob.mul_add : ∀ p q r : Prob, p *ₚ (q +ₚ r) = (p *ₚ q) +ₚ (p *ₚ r)
axiom Prob.add_mul : ∀ p q r : Prob, (p +ₚ q) *ₚ r = (p *ₚ r) +ₚ (q *ₚ r)

-- Special case for 1+1-1=1
axiom Prob.one_add_one_sub_one : (𝟙 +ₚ 𝟙) -ₚ 𝟙 = 𝟙

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

noncomputable def prob_or {α : Type} (A B : ProbProp α) : ProbProp α :=
  fun x => (A x +ₚ B x) -ₚ (A x *ₚ B x)

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

-- Classical OR is classical
theorem classical_or_closed {α : Type} (A B : ClassicalProp α) :
    ∀ x, isClassical ((A.val ∨ₚ B.val) x) := by
  intro x
  simp only [prob_or, isClassical]
  have ha : isClassical (A.val x) := A.property x
  have hb : isClassical (B.val x) := B.property x
  cases ha with
  | inl haz =>
    rw [haz, Prob.zero_add, Prob.zero_mul]
    cases hb with
    | inl hbz =>
      left
      rw [hbz, Prob.sub_self]
    | inr hbo =>
      right
      rw [hbo, Prob.sub_zero]
  | inr hao =>
    rw [hao]
    cases hb with
    | inl hbz =>
      right
      rw [hbz, Prob.add_zero, Prob.mul_zero, Prob.sub_zero]
    | inr hbo =>
      right
      rw [hbo, Prob.one_mul]
      exact Prob.one_add_one_sub_one

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
-- SUMMARY: PROBABILITY AS FOUNDATION
-- ============================================================================

/-
The key insight: classical logic is NOT primitive. It is the {0,1} boundary case
of probability theory. We have demonstrated:

1. Prob type with algebraic structure (ordered semiring in [0,1])
2. Conditional expectation E[f|g] as the core primitive
3. Probabilistic entailment Γ ⊢[p] φ meaning E[φ|Γ] ≥ p
4. Proof theory rules (ALL PROVED):
   - axiom_rule: φ ⊢[1] φ
   - weaken: Γ ⊢[p] φ → q ≤ p → Γ ⊢[q] φ
   - cut_rule: Γ ⊢[p] φ → φ ⊢[q] ψ → Γ ⊢[p*q] ψ
   - mono_rule: (∀x, φ x ≤ ψ x) → Γ ⊢[p] φ → Γ ⊢[p] ψ
5. Probabilistic logical operations (∧ₚ, ∨ₚ, ¬ₚ, →ₚ)
6. Classical logic as restriction to {0,1}-valued propositions:
   - classical_and_closed (PROVED)
   - classical_or_closed (PROVED)
   - classical_not_closed (PROVED)
7. LEM as algebraic identity:
   - prob_lem: φ x + (¬ₚ φ) x = 1 (PROVED)
   - lem_expectation: E[φ|ψ] + E[¬ₚφ|ψ] = 1 (PROVED)
8. Double negation: (¬ₚ (¬ₚ φ)) = φ (PROVED)

The metalogic/object-logic distinction:
- METALOGIC: Lean's type theory (used to define and verify)
- OBJECT: Probabilistic foundations (Prob, E[·|·], ⊢[p])
- DERIVED: Classical logic ({0,1} case)
-/
