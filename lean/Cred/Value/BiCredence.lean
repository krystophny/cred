/-
  Cred Value: BiCredence (Two-Coordinate Value, FDE/Belnap)

  A BiCredence pairs a positive credence (pos) and a negative credence (neg)
  independently, without requiring pos + neg ≤ 1 or pos + neg ≥ 1.
  The four corners (0,0), (1,0), (0,1), (1,1) collapse exactly to the four
  Belnap-Dunn FDE truth values: neither, trueOnly, falseOnly, both.

  Operations follow the FDE bilattice: negation swaps coordinates, conjunction
  takes the positive meet via ⊗ and the negative join via ⊔, disjunction is
  dual. All proofs are complete; no sorry.
-/

import Cred.Core.Value

namespace Cred

open Credence

/-! ## BiCredence Structure -/

/-- A two-coordinate credence: independent positive and negative evidence. -/
@[ext]
structure BiCredence where
  pos : Credence
  neg : Credence

namespace BiCredence

/-! ## Operations -/

/-- Negation swaps positive and negative coordinates. -/
def bneg (b : BiCredence) : BiCredence := ⟨b.neg, b.pos⟩

prefix:80 "~ᵦ" => bneg

@[simp] theorem bneg_pos (b : BiCredence) : (~ᵦb).pos = b.neg := rfl
@[simp] theorem bneg_neg (b : BiCredence) : (~ᵦb).neg = b.pos := rfl

/-- Conjunction: positive evidence multiplies (⊗), negative evidence accumulates (⊔). -/
def bconj (b₁ b₂ : BiCredence) : BiCredence :=
  ⟨b₁.pos ⊗ b₂.pos, b₁.neg ⊔ b₂.neg⟩

infixl:70 " ⊗ᵦ " => bconj

@[simp] theorem bconj_pos (b₁ b₂ : BiCredence) : (b₁ ⊗ᵦ b₂).pos = b₁.pos ⊗ b₂.pos := rfl
@[simp] theorem bconj_neg (b₁ b₂ : BiCredence) : (b₁ ⊗ᵦ b₂).neg = b₁.neg ⊔ b₂.neg := rfl

/-- Disjunction: De Morgan dual of conjunction via bneg. -/
def bdisj (b₁ b₂ : BiCredence) : BiCredence := ~ᵦ(~ᵦb₁ ⊗ᵦ ~ᵦb₂)

infixl:65 " ⊔ᵦ " => bdisj

@[simp] theorem bdisj_pos (b₁ b₂ : BiCredence) : (b₁ ⊔ᵦ b₂).pos = b₁.pos ⊔ b₂.pos := by
  simp [bdisj, bneg, bconj]

@[simp] theorem bdisj_neg (b₁ b₂ : BiCredence) : (b₁ ⊔ᵦ b₂).neg = b₁.neg ⊗ b₂.neg := by
  simp [bdisj, bneg, bconj]

/-! ## Four Corners -/

/-- Neither: no positive evidence, no negative evidence. FDE ⊥. -/
def neither : BiCredence := ⟨0, 0⟩

/-- TrueOnly: full positive evidence, no negative evidence. FDE ⊤. -/
def trueOnly : BiCredence := ⟨1, 0⟩

/-- FalseOnly: no positive evidence, full negative evidence. FDE ⊥ (false). -/
def falseOnly : BiCredence := ⟨0, 1⟩

/-- Both: full positive and negative evidence simultaneously. FDE ⊤∧⊥. -/
def both : BiCredence := ⟨1, 1⟩

/-! ## Negation Corner Theorems -/

/-- Negation swaps trueOnly and falseOnly. -/
theorem bneg_trueOnly : ~ᵦtrueOnly = falseOnly := by
  ext <;> simp [bneg, trueOnly, falseOnly]

theorem bneg_falseOnly : ~ᵦfalseOnly = trueOnly := by
  ext <;> simp [bneg, trueOnly, falseOnly]

/-- Negation fixes both. -/
theorem bneg_both : ~ᵦboth = both := by
  ext <;> simp [bneg, both]

/-- Negation fixes neither. -/
theorem bneg_neither : ~ᵦneither = neither := by
  ext <;> simp [bneg, neither]

/-- Negation is involutive. -/
@[simp] theorem bneg_bneg (b : BiCredence) : ~ᵦ~ᵦb = b := by
  ext <;> simp [bneg]

/-! ## FDE / Belnap Collapse -/

/-- The four Belnap-Dunn FDE truth values. -/
inductive FDE : Type
  | neither : FDE
  | trueOnly : FDE
  | falseOnly : FDE
  | both : FDE

/-- A BiCredence is certain-positive when pos = 1. -/
def certainPos (b : BiCredence) : Prop := b.pos = 1

/-- A BiCredence is certain-negative when neg = 1. -/
def certainNeg (b : BiCredence) : Prop := b.neg = 1

open Classical in
/-- Collapse by thresholding each coordinate at certainty (= 1).
    Uses classical logic; the four corners have decidable membership. -/
noncomputable def toFDE (b : BiCredence) : FDE :=
  if b.pos = 1 ∧ b.neg ≠ 1 then FDE.trueOnly
  else if b.pos ≠ 1 ∧ b.neg = 1 then FDE.falseOnly
  else if b.pos = 1 ∧ b.neg = 1 then FDE.both
  else FDE.neither

-- 0 ≠ 1 as Credence, needed to discharge corner proofs.
private theorem zero_ne_one_cred : (0 : Credence) ≠ 1 := by
  intro h; have := congrArg Credence.val h; simp [zero_val, one_val] at this

/-- The neither corner maps to FDE.neither. -/
theorem toFDE_neither : toFDE neither = FDE.neither := by
  have h : (0 : Credence) ≠ 1 := zero_ne_one_cred
  simp only [toFDE, neither]
  rw [if_neg (fun ⟨heq, _⟩ => h heq), if_neg (fun ⟨_, heq⟩ => h heq),
      if_neg (fun ⟨heq, _⟩ => h heq)]

/-- The trueOnly corner maps to FDE.trueOnly. -/
theorem toFDE_trueOnly : toFDE trueOnly = FDE.trueOnly := by
  have h : (0 : Credence) ≠ 1 := zero_ne_one_cred
  simp only [toFDE, trueOnly]
  rw [if_pos ⟨rfl, h⟩]

/-- The falseOnly corner maps to FDE.falseOnly. -/
theorem toFDE_falseOnly : toFDE falseOnly = FDE.falseOnly := by
  have h : (0 : Credence) ≠ 1 := zero_ne_one_cred
  simp only [toFDE, falseOnly]
  rw [if_neg (fun ⟨heq, _⟩ => h heq), if_pos ⟨h, rfl⟩]

/-- The both corner maps to FDE.both. -/
theorem toFDE_both : toFDE both = FDE.both := by
  have hpos : both.pos = 1 := rfl
  have hneg : both.neg = 1 := rfl
  unfold toFDE
  rw [if_neg (fun ⟨_, hne⟩ => hne hneg), if_neg (fun ⟨hne, _⟩ => hne hpos),
      if_pos ⟨hpos, hneg⟩]

/-! ## Positive Projection -/

/-- Project to the positive coordinate. -/
def projPos (b : BiCredence) : Credence := b.pos

/-! projPos is a homomorphism for bneg: it maps negation to negation only on
    the falseOnly/trueOnly fragment where pos and neg are complementary. For the
    general case, the projection of negation equals the negation of the negative
    coordinate, not of the positive one. The honest fragment is: projPos commutes
    with bneg exactly when pos = ~neg (the "consistent" sub-domain). -/

/-- projPos of bneg equals the neg field of b. -/
@[simp] theorem projPos_bneg (b : BiCredence) : projPos (~ᵦb) = b.neg := rfl

/-- projPos is a strict homomorphism for conjunction on the positive axis. -/
theorem projPos_bconj (b₁ b₂ : BiCredence) :
    projPos (b₁ ⊗ᵦ b₂) = projPos b₁ ⊗ projPos b₂ := rfl

/-- projPos is a strict homomorphism for disjunction on the positive axis. -/
theorem projPos_bdisj (b₁ b₂ : BiCredence) :
    projPos (b₁ ⊔ᵦ b₂) = projPos b₁ ⊔ projPos b₂ := by
  simp [projPos, bdisj_pos]

/-- On the complementary fragment (neg = ~pos), projPos commutes with bneg
    via the credence negation ~. This is the exact negation-homomorphism claim. -/
theorem projPos_bneg_complementary (b : BiCredence) (h : b.neg = ~b.pos) :
    projPos (~ᵦb) = ~(projPos b) := by
  simp [projPos, bneg, h]

end BiCredence

end Cred
