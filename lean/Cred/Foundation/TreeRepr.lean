/-
  Cred Foundation: pure-arithmetic core of tree representability

  A natural number codes a binary tree by the pairing recursion `0` for the leaf
  and `n+1` for a node whose two children are the unpairing of `n`. The
  predicate `isTree` decides this shape by well-founded recursion on the
  children, which are bounded by the parent under `Nat.unpair`.

  The representability bridge is `isTree_iff_beta`: `n` codes a tree exactly when
  there is a single number `N` whose Gödel-beta table `Nat.beta N ·` marks `n`
  with `1` and is locally coherent up to `n`. Coherence at `k` (`CohereNat`)
  says the table entry is `1` iff `k` is a leaf or both unpaired children of
  `k-1` are themselves marked `1`. This is the arithmetized course-of-values
  step; no object-level Cred formula appears yet.
-/

import Cred.Foundation.Beta

namespace Cred
namespace Foundation
namespace arithQ

/-- Decide whether `n` codes a binary tree: `0` is the leaf, and `n+1` codes a
    node whose children are `(Nat.unpair n).1` and `(Nat.unpair n).2`, each of
    which must itself code a tree. The children are strictly smaller than `n+1`,
    so the recursion terminates. -/
def isTree : Nat → Bool
  | 0 => true
  | (n + 1) => isTree (Nat.unpair n).1 && isTree (Nat.unpair n).2
  termination_by n => n
  decreasing_by
    · exact Nat.lt_succ_of_le (Nat.unpair_left_le n)
    · exact Nat.lt_succ_of_le (Nat.unpair_right_le n)

@[simp] theorem isTree_zero : isTree 0 = true := by
  rw [isTree]

theorem isTree_succ (n : Nat) :
    isTree (n + 1) = (isTree (Nat.unpair n).1 && isTree (Nat.unpair n).2) := by
  rw [isTree]

/-- Local coherence of the beta table `Nat.beta N ·` at index `k`: the entry is
    `1` exactly when `k` is the leaf `0`, or `k` is a node (`0 < k`) whose two
    unpaired children of `k-1` are both marked `1`. -/
def CohereNat (N k : Nat) : Prop :=
  Nat.beta N k = 1 ↔
    (k = 0 ∨
      (0 < k ∧
        Nat.beta N (Nat.unpair (k - 1)).1 = 1 ∧
        Nat.beta N (Nat.unpair (k - 1)).2 = 1))

/-- Pure-arithmetic representability of the tree predicate: `n` codes a tree
    exactly when some single number `N` carries a beta table that marks `n` and
    is locally coherent everywhere up to `n`. -/
theorem isTree_iff_beta (n : Nat) :
    isTree n = true ↔
      ∃ N : Nat, Nat.beta N n = 1 ∧ ∀ k, k ≤ n → CohereNat N k := by
  constructor
  · -- (→) build the explicit table and read it back with the beta lemma.
    intro htree
    set l : List Nat :=
      (List.range (n + 1)).map (fun k => if isTree k = true then 1 else 0)
      with hl
    have hlen : l.length = n + 1 := by
      simp [hl]
    refine ⟨Nat.unbeta l, ?_, ?_⟩
    -- read back the entry at index `k ≤ n`.
    case _ =>
      have hbeta : ∀ k, k ≤ n →
          Nat.beta (Nat.unbeta l) k = (if isTree k = true then 1 else 0) := by
        intro k hk
        have hk' : k < l.length := by
          rw [hlen]; exact Nat.lt_succ_of_le hk
        have := Nat.beta_unbeta_coe l ⟨k, hk'⟩
        rw [this]
        have hkr : k < (List.range (n + 1)).length := by
          simpa using Nat.lt_succ_of_le hk
        simp [hl, List.getElem_map, List.getElem_range]
      rw [hbeta n (le_refl n)]
      simp [htree]
    case _ =>
      -- coherence: rewrite each beta entry through `hbeta`.
      have hbeta : ∀ k, k ≤ n →
          Nat.beta (Nat.unbeta l) k = (if isTree k = true then 1 else 0) := by
        intro k hk
        have hk' : k < l.length := by
          rw [hlen]; exact Nat.lt_succ_of_le hk
        have := Nat.beta_unbeta_coe l ⟨k, hk'⟩
        rw [this]
        simp [hl, List.getElem_map, List.getElem_range]
      intro k hk
      -- `Nat.beta N k = 1 ↔ isTree k = true`.
      have hk1 : Nat.beta (Nat.unbeta l) k = 1 ↔ isTree k = true := by
        rw [hbeta k hk]
        by_cases hik : isTree k = true <;> simp [hik]
      unfold CohereNat
      rw [hk1]
      -- structural characterization of `isTree k`.
      cases k with
      | zero => simp
      | succ m =>
        have hsucc : isTree (m + 1) = true ↔
            (isTree (Nat.unpair m).1 = true ∧ isTree (Nat.unpair m).2 = true) := by
          rw [isTree_succ, Bool.and_eq_true]
        -- children indices are `≤ n` so we can rewrite their betas too.
        have hle1 : (Nat.unpair m).1 ≤ n :=
          le_trans (le_trans (Nat.unpair_left_le m) (Nat.le_succ m)) hk
        have hle2 : (Nat.unpair m).2 ≤ n :=
          le_trans (le_trans (Nat.unpair_right_le m) (Nat.le_succ m)) hk
        have hc1 : Nat.beta (Nat.unbeta l) (Nat.unpair (m + 1 - 1)).1 = 1 ↔
            isTree (Nat.unpair m).1 = true := by
          simp only [Nat.add_sub_cancel]
          rw [hbeta _ hle1]
          by_cases h : isTree (Nat.unpair m).1 = true <;> simp [h]
        have hc2 : Nat.beta (Nat.unbeta l) (Nat.unpair (m + 1 - 1)).2 = 1 ↔
            isTree (Nat.unpair m).2 = true := by
          simp only [Nat.add_sub_cancel]
          rw [hbeta _ hle2]
          by_cases h : isTree (Nat.unpair m).2 = true <;> simp [h]
        rw [hsucc, hc1, hc2]
        constructor
        · intro h; exact Or.inr ⟨Nat.succ_pos m, h.1, h.2⟩
        · rintro (h | ⟨_, hl, hr⟩)
          · exact absurd h (Nat.succ_ne_zero m)
          · exact ⟨hl, hr⟩
  · -- (←) strong induction reading the table back into the predicate.
    rintro ⟨N, hN, hcoh⟩
    suffices h : ∀ k, k ≤ n → Nat.beta N k = 1 → isTree k = true by
      exact h n (le_refl n) hN
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hbk
      have hck : CohereNat N k := hcoh k hk
      rcases (hck.mp hbk) with hzero | ⟨hpos, hb1, hb2⟩
      · subst hzero; exact isTree_zero
      · -- `k = m + 1`, children of `m` are `< k` and `≤ n`.
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        rw [Nat.succ_sub_one] at hb1 hb2
        have hlt1 : (Nat.unpair m).1 < m + 1 :=
          Nat.lt_succ_of_le (Nat.unpair_left_le m)
        have hlt2 : (Nat.unpair m).2 < m + 1 :=
          Nat.lt_succ_of_le (Nat.unpair_right_le m)
        have hle1 : (Nat.unpair m).1 ≤ n := le_trans (Nat.le_of_lt hlt1) hk
        have hle2 : (Nat.unpair m).2 ≤ n := le_trans (Nat.le_of_lt hlt2) hk
        have ht1 : isTree (Nat.unpair m).1 = true := ih _ hlt1 hle1 hb1
        have ht2 : isTree (Nat.unpair m).2 = true := ih _ hlt2 hle2 hb2
        rw [isTree_succ, Bool.and_eq_true]
        exact ⟨ht1, ht2⟩

end arithQ
end Foundation
end Cred
