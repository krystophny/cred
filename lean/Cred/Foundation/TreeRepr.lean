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

/-! ## Object-language representation of the tree predicate

The arithmetic core above is now lifted to a single object formula over the
Robinson Q signature. The course-of-values witness `N` becomes an existential
binder; coherence becomes a bounded universal over `k ≤ x`, with each step
phrased through the already-verified pairing and beta graphs. -/

open Credence

/-- A universal over a crisp family is certain iff every instance is certain. -/
private theorem crisp_all_one_iff (f : Nat → Credence)
    (hf : ∀ c, f c = 0 ∨ f c = 1) :
    natModel.all f = 1 ↔ ∀ c, f c = 1 := by
  constructor
  · intro h c
    rcases hf c with h0 | h1
    · exfalso
      have hle : (natModel.all f).val ≤ (f c).val :=
        natModel_quantifierLaws.all_le_instance f c
      rw [h, h0, Credence.one_val, Credence.zero_val] at hle
      norm_num at hle
    · exact h1
  · intro h
    exact natModel_all_eq_one h

/-- A universal over a crisp family is crisp. -/
private theorem crisp_all_crisp (f : Nat → Credence)
    (hf : ∀ c, f c = 0 ∨ f c = 1) :
    natModel.all f = 0 ∨ natModel.all f = 1 := by
  by_cases h : ∀ c, f c = 1
  · exact Or.inr ((crisp_all_one_iff f hf).2 h)
  · left
    push_neg at h
    obtain ⟨c, hc⟩ := h
    have hc0 : f c = 0 := (hf c).resolve_right hc
    apply Credence.ext
    rw [Credence.zero_val]
    have hle : (natModel.all f).val ≤ (f c).val :=
      natModel_quantifierLaws.all_le_instance f c
    rw [hc0, Credence.zero_val] at hle
    exact le_antisymm hle (natModel.all f).nonneg

/-- `oneT` is the object numeral `1`. -/
private def oneT : ArithQTerm := succT zeroT

@[simp] private theorem eval_oneT (env : natModel.Assignment) :
    natModel.evalTerm env oneT = (1 : Nat) := rfl

/-- Material implication on crisp credences. -/
private theorem impCred_one_iff {a b : Credence}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    ~a ⊔ b = 1 ↔ (a = 1 → b = 1) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst ha <;> subst hb <;>
    simp [Credence.neg_zero, Credence.neg_one, Credence.one_disj,
      Credence.zero_disj, Credence.disj_one, Credence.disj_zero]

/-- `impF` evaluates crisply. -/
private theorem impF_crisp (env : natModel.Assignment) (φ ψ : ArithQFormula)
    (hφ : natModel.evalFormula env φ = 0 ∨ natModel.evalFormula env φ = 1)
    (hψ : natModel.evalFormula env ψ = 0 ∨ natModel.evalFormula env ψ = 1) :
    natModel.evalFormula env (impF φ ψ) = 0 ∨
      natModel.evalFormula env (impF φ ψ) = 1 := by
  have hneg : ~(natModel.evalFormula env φ) = 0 ∨
      ~(natModel.evalFormula env φ) = 1 := by
    rcases hφ with h | h <;> rw [h]
    · exact Or.inr Credence.neg_zero
    · exact Or.inl Credence.neg_one
  show ~(natModel.evalFormula env φ) ⊔ natModel.evalFormula env ψ = 0 ∨
    ~(natModel.evalFormula env φ) ⊔ natModel.evalFormula env ψ = 1
  rcases hneg with h | h <;> rcases hψ with h' | h' <;> rw [h, h'] <;>
    simp [Credence.one_disj, Credence.zero_disj, Credence.disj_one,
      Credence.disj_zero]

/-- `impF` is designated iff designation of the antecedent forces the
    consequent. -/
private theorem impF_eval_one_iff (env : natModel.Assignment)
    (φ ψ : ArithQFormula)
    (hφ : natModel.evalFormula env φ = 0 ∨ natModel.evalFormula env φ = 1)
    (hψ : natModel.evalFormula env ψ = 0 ∨ natModel.evalFormula env ψ = 1) :
    natModel.evalFormula env (impF φ ψ) = 1 ↔
      (natModel.evalFormula env φ = 1 → natModel.evalFormula env ψ = 1) := by
  rw [impF]
  show ~(natModel.evalFormula env φ) ⊔ natModel.evalFormula env ψ = 1 ↔ _
  exact impCred_one_iff hφ hψ

/-- Biconditional via two material implications. -/
private def iffF (φ ψ : ArithQFormula) : ArithQFormula :=
  .conj (impF φ ψ) (impF ψ φ)

/-- `iffF` is designated iff the two formulas are designated together. -/
private theorem iffF_eval_one_iff (env : natModel.Assignment)
    (φ ψ : ArithQFormula)
    (hφ : natModel.evalFormula env φ = 0 ∨ natModel.evalFormula env φ = 1)
    (hψ : natModel.evalFormula env ψ = 0 ∨ natModel.evalFormula env ψ = 1) :
    natModel.evalFormula env (iffF φ ψ) = 1 ↔
      (natModel.evalFormula env φ = 1 ↔ natModel.evalFormula env ψ = 1) := by
  rw [iffF]
  show natModel.evalFormula env (impF φ ψ) ⊗
      natModel.evalFormula env (impF ψ φ) = 1 ↔ _
  rw [conj_crisp_one_iff (impF_crisp env φ ψ hφ hψ) (impF_crisp env ψ φ hψ hφ),
    impF_eval_one_iff env φ ψ hφ hψ, impF_eval_one_iff env ψ φ hψ hφ]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩

/-- `iffF` evaluates crisply. -/
private theorem iffF_crisp (env : natModel.Assignment) (φ ψ : ArithQFormula)
    (hφ : natModel.evalFormula env φ = 0 ∨ natModel.evalFormula env φ = 1)
    (hψ : natModel.evalFormula env ψ = 0 ∨ natModel.evalFormula env ψ = 1) :
    natModel.evalFormula env (iffF φ ψ) = 0 ∨
      natModel.evalFormula env (iffF φ ψ) = 1 := by
  rw [iffF]
  show natModel.evalFormula env (impF φ ψ) ⊗
      natModel.evalFormula env (impF ψ φ) = 0 ∨ _
  exact conj_crisp (impF_crisp env φ ψ hφ hψ) (impF_crisp env ψ φ hψ hφ)

/-! ### Term-level crispness and evaluation reused from the beta bricks

The beta and pairing graphs are placed at arbitrary argument terms inside
`treeFormula`, so their crisp evaluation is needed at the term level. The
numeral-only exports of `Beta.lean` do not suffice; the term-level chain is
reconstructed here from the public connective and order lemmas. -/

/-- A disjunction of crisp credences is crisp. -/
private theorem disj_crisp' {a b : Credence}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    a ⊔ b = 0 ∨ a ⊔ b = 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst ha <;> subst hb <;>
    simp [Credence.zero_disj, Credence.disj_zero, Credence.disj_one,
      Credence.one_disj]

/-- An existential over a crisp body is crisp. -/
private theorem existsE_crisp' (env : natModel.Assignment) (φ : ArithQFormula)
    (hcrisp : ∀ c : Nat,
      natModel.evalFormula (Structure.update natModel env c) φ = 0 ∨
      natModel.evalFormula (Structure.update natModel env c) φ = 1) :
    natModel.evalFormula env (.existsE φ) = 0 ∨
      natModel.evalFormula env (.existsE φ) = 1 := by
  by_cases h : ∃ c : Nat,
      natModel.evalFormula (Structure.update natModel env c) φ = 1
  · exact Or.inr ((existsE_crisp_one_iff env φ hcrisp).2 h)
  · left
    have hzero : (fun c : Nat =>
        natModel.evalFormula (Structure.update natModel env c) φ) =
          fun _ : Nat => (0 : Credence) := by
      funext c
      rcases hcrisp c with h0 | h1
      · exact h0
      · exact absurd ⟨c, h1⟩ h
    show natModel.ex (fun c : Nat =>
        natModel.evalFormula (Structure.update natModel env c) φ) = 0
    exact (congrArg natModel.ex hzero).trans natModel_quantifierLaws.ex_zero

/-- The pairing graph evaluates crisply at every term tuple. -/
private theorem pairGraph_crisp' (env : natModel.Assignment)
    (x y z : ArithQTerm) :
    natModel.evalFormula env (pairGraph x y z) = 0 ∨
      natModel.evalFormula env (pairGraph x y z) = 1 := by
  rw [pairGraph]
  show natModel.evalFormula env
        (.conj (ltF x y) (.equal z (addT (mulT y y) x))) ⊔
      natModel.evalFormula env
        (.conj (leF y x) (.equal z (addT (addT (mulT x x) x) y))) = 0 ∨ _
  exact disj_crisp'
    (conj_crisp (ltF_crisp env x y) (eqAtom_crisp env z (addT (mulT y y) x)))
    (conj_crisp (leF_crisp env y x)
      (eqAtom_crisp env z (addT (addT (mulT x x) x) y)))

/-- The unpairing graph evaluates crisply at every term tuple. -/
private theorem unpairGraph_crisp' (env : natModel.Assignment)
    (z x y : ArithQTerm) :
    natModel.evalFormula env (unpairGraph z x y) = 0 ∨
      natModel.evalFormula env (unpairGraph z x y) = 1 :=
  pairGraph_crisp' env x y z

/-- The unpairing graph at arbitrary terms: designated exactly when `⟦z⟧`
    unpairs into `(⟦x⟧, ⟦y⟧)`. -/
private theorem unpairGraph_eval_one_iff' (env : natModel.Assignment)
    (z x y : ArithQTerm) :
    natModel.evalFormula env (unpairGraph z x y) = 1 ↔
      Nat.unpair (natModel.evalTerm env z) =
        (natModel.evalTerm env x, natModel.evalTerm env y) := by
  rw [unpairGraph, pairGraph_eval_one_iff, pair_eq_iff_unpair]

/-- The modulo graph evaluates crisply at every term tuple. -/
private theorem modGraph_crisp' (env : natModel.Assignment)
    (a m r : ArithQTerm) :
    natModel.evalFormula env (modGraph a m r) = 0 ∨
      natModel.evalFormula env (modGraph a m r) = 1 := by
  rw [modGraph]
  exact existsE_crisp' env _
    (fun _ => conj_crisp (eqAtom_crisp _ _ _) (ltF_crisp _ _ _))

/-- The beta graph evaluates crisply at every term tuple. -/
private theorem betaGraph_crisp' (env : natModel.Assignment)
    (a d i w : ArithQTerm) :
    natModel.evalFormula env (betaGraph a d i w) = 0 ∨
      natModel.evalFormula env (betaGraph a d i w) = 1 :=
  modGraph_crisp' env a (succT (mulT (succT i) d)) w

/-- A parameter shifted under the binder evaluates as it did outside. -/
private theorem eval_rename_succ' (env : natModel.Assignment)
    (q : natModel.Domain) (t : ArithQTerm) :
    natModel.evalTerm (Structure.update natModel env q)
        (Term.rename Nat.succ t) =
      natModel.evalTerm env t := by
  rw [Structure.evalTerm_rename]; rfl

/-- Witness arithmetic for the modulo graph. -/
private theorem mod_witness_iff' (a m r : Nat) (hm : 0 < m) :
    (∃ q : Nat, a = q * m + r ∧ r < m) ↔ r = a % m := by
  constructor
  · rintro ⟨q, hq, hr⟩
    rw [hq, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  · intro h
    refine ⟨a / m, ?_, ?_⟩
    · rw [h, Nat.mul_comm]; exact (Nat.div_add_mod a m).symm
    · rw [h]; exact Nat.mod_lt a hm

/-- Term-level evaluation of the modulo graph, for any positive modulus term. -/
private theorem modGraph_eval_one_iff' (env : natModel.Assignment)
    (A M R : ArithQTerm) (hm : 0 < natModel.evalTerm env M) :
    natModel.evalFormula env (modGraph A M R) = 1 ↔
      natModel.evalTerm env R =
        natModel.evalTerm env A % natModel.evalTerm env M := by
  have hbody : ∀ q : natModel.Domain,
      natModel.evalFormula (Structure.update natModel env q)
        (.conj
          (.equal (Term.rename Nat.succ A)
            (addT (mulT (v 0) (Term.rename Nat.succ M))
              (Term.rename Nat.succ R)))
          (ltF (Term.rename Nat.succ R) (Term.rename Nat.succ M))) = 1 ↔
        natModel.evalTerm env A =
            q * natModel.evalTerm env M + natModel.evalTerm env R ∧
          natModel.evalTerm env R < natModel.evalTerm env M := by
    intro q
    have hrhs : natModel.evalTerm (Structure.update natModel env q)
        (addT (mulT (v 0) (Term.rename Nat.succ M)) (Term.rename Nat.succ R)) =
          q * natModel.evalTerm env M + natModel.evalTerm env R := by
      show natModel.func .add
          [natModel.func .mul
            [Structure.update natModel env q 0,
             natModel.evalTerm (Structure.update natModel env q)
               (Term.rename Nat.succ M)],
           natModel.evalTerm (Structure.update natModel env q)
             (Term.rename Nat.succ R)] = _
      rw [eval_rename_succ', eval_rename_succ']; rfl
    show natModel.evalFormula (Structure.update natModel env q)
        (.equal (Term.rename Nat.succ A)
          (addT (mulT (v 0) (Term.rename Nat.succ M))
            (Term.rename Nat.succ R))) ⊗
      natModel.evalFormula (Structure.update natModel env q)
        (ltF (Term.rename Nat.succ R) (Term.rename Nat.succ M)) = 1 ↔ _
    rw [conj_crisp_one_iff (eqAtom_crisp _ _ _) (ltF_crisp _ _ _),
      eqAtom_eval_one_iff, ltF_eval_one_iff, eval_rename_succ', hrhs,
      eval_rename_succ', eval_rename_succ']
  have hcrisp : ∀ q : Nat,
      natModel.evalFormula (Structure.update natModel env q)
        (.conj
          (.equal (Term.rename Nat.succ A)
            (addT (mulT (v 0) (Term.rename Nat.succ M))
              (Term.rename Nat.succ R)))
          (ltF (Term.rename Nat.succ R) (Term.rename Nat.succ M))) = 0 ∨
      natModel.evalFormula (Structure.update natModel env q)
        (.conj
          (.equal (Term.rename Nat.succ A)
            (addT (mulT (v 0) (Term.rename Nat.succ M))
              (Term.rename Nat.succ R)))
          (ltF (Term.rename Nat.succ R) (Term.rename Nat.succ M))) = 1 :=
    fun _ => conj_crisp (eqAtom_crisp _ _ _) (ltF_crisp _ _ _)
  rw [modGraph, existsE_crisp_one_iff env _ hcrisp]
  exact (exists_congr hbody).trans (mod_witness_iff' _ _ _ hm)

/-- Term-level evaluation of the beta graph: designated exactly when `⟦w⟧` is
    the remainder of `⟦a⟧` by `1 + (⟦i⟧+1) * ⟦d⟧`. -/
private theorem betaGraph_eval_one_iff' (env : natModel.Assignment)
    (A D I W : ArithQTerm) :
    natModel.evalFormula env (betaGraph A D I W) = 1 ↔
      natModel.evalTerm env W =
        natModel.evalTerm env A %
          (1 + (natModel.evalTerm env I + 1) * natModel.evalTerm env D) := by
  have hmod : natModel.evalTerm env (succT (mulT (succT I) D)) =
      1 + (natModel.evalTerm env I + 1) * natModel.evalTerm env D := by
    show natModel.func .succ
        [natModel.func .mul
          [natModel.func .succ [natModel.evalTerm env I],
           natModel.evalTerm env D]] = _
    show (natModel.evalTerm env I + 1) * natModel.evalTerm env D + 1 = _
    exact Nat.add_comm _ _
  rw [betaGraph,
    modGraph_eval_one_iff' env _ _ _
      (by rw [hmod]
          exact Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_add_right 1 _)),
    hmod]

/-- Lift a term past two fresh binders. -/
private def shift2' (t : ArithQTerm) : ArithQTerm :=
  Term.rename (Nat.succ ∘ Nat.succ) t

/-- A term shifted under two binders evaluates as it did outside. -/
private theorem eval_shift2' (env : natModel.Assignment)
    (a d : natModel.Domain) (t : ArithQTerm) :
    natModel.evalTerm
        (Structure.update natModel (Structure.update natModel env a) d)
        (shift2' t) =
      natModel.evalTerm env t := by
  rw [shift2', Structure.evalTerm_rename]; rfl

/-- Single-code beta graph, self-contained over the public `unpairGraph` and
    `betaGraph`. The two unpaired halves of the code `n` are bound existentially
    (`a := v 1`, `d := v 0`), then the remainder is read off. -/
private def betaNF (n i w : ArithQTerm) : ArithQFormula :=
  .existsE (.existsE
    (.conj (unpairGraph (shift2' n) (Term.var 1) (Term.var 0))
      (betaGraph (Term.var 1) (Term.var 0) (shift2' i) (shift2' w))))

/-- Witness arithmetic: the two unpaired halves of `n` exist exactly when `w`
    is `Nat.beta n i`. -/
private theorem betaNF_witness_iff (n i w : Nat) :
    (∃ a : Nat, ∃ d : Nat,
        Nat.unpair n = (a, d) ∧ w = a % (1 + (i + 1) * d)) ↔
      w = Nat.beta n i := by
  constructor
  · rintro ⟨a, d, hpair, hw⟩
    have ha : (Nat.unpair n).1 = a := by rw [hpair]
    have hd : (Nat.unpair n).2 = d := by rw [hpair]
    show w = (Nat.unpair n).1 % ((i + 1) * (Nat.unpair n).2 + 1)
    rw [ha, hd, Nat.add_comm ((i + 1) * d) 1]
    exact hw
  · intro hw
    refine ⟨(Nat.unpair n).1, (Nat.unpair n).2, rfl, ?_⟩
    rw [Nat.add_comm 1 ((i + 1) * (Nat.unpair n).2)]
    exact hw

/-- Term-level evaluation of the single-code beta graph: designated exactly
    when `⟦w⟧ = Nat.beta ⟦n⟧ ⟦i⟧`. -/
private theorem betaNF_eval_one_iff (env : natModel.Assignment)
    (N I W : ArithQTerm) :
    natModel.evalFormula env (betaNF N I W) = 1 ↔
      natModel.evalTerm env W =
        Nat.beta (natModel.evalTerm env N) (natModel.evalTerm env I) := by
  -- crispness of the matrix
  have hcrisp : ∀ a d : Nat,
      natModel.evalFormula
          (Structure.update natModel (Structure.update natModel env a) d)
          (.conj (unpairGraph (shift2' N) (Term.var 1) (Term.var 0))
            (betaGraph (Term.var 1) (Term.var 0) (shift2' I) (shift2' W))) = 0 ∨
        natModel.evalFormula
          (Structure.update natModel (Structure.update natModel env a) d)
          (.conj (unpairGraph (shift2' N) (Term.var 1) (Term.var 0))
            (betaGraph (Term.var 1) (Term.var 0) (shift2' I) (shift2' W))) = 1 :=
    fun a d =>
      conj_crisp (unpairGraph_crisp' _ _ _ _) (betaGraph_crisp' _ _ _ _ _)
  have hinner : ∀ a : Nat,
      natModel.evalFormula (Structure.update natModel env a)
          (.existsE (.conj (unpairGraph (shift2' N) (Term.var 1) (Term.var 0))
            (betaGraph (Term.var 1) (Term.var 0) (shift2' I) (shift2' W)))) = 0 ∨
        natModel.evalFormula (Structure.update natModel env a)
          (.existsE (.conj (unpairGraph (shift2' N) (Term.var 1) (Term.var 0))
            (betaGraph (Term.var 1) (Term.var 0) (shift2' I) (shift2' W)))) = 1 :=
    fun a => existsE_crisp' _ _ (hcrisp a)
  rw [betaNF, existsE_crisp_one_iff env _ hinner]
  refine Iff.trans (exists_congr fun a => ?_)
    (betaNF_witness_iff (natModel.evalTerm env N) (natModel.evalTerm env I)
      (natModel.evalTerm env W))
  rw [existsE_crisp_one_iff _ _ (hcrisp a)]
  refine exists_congr fun d => ?_
  have eN : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (shift2' N) = natModel.evalTerm env N := eval_shift2' env a d N
  have eI : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (shift2' I) = natModel.evalTerm env I := eval_shift2' env a d I
  have eW : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (shift2' W) = natModel.evalTerm env W := eval_shift2' env a d W
  have ea : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (Term.var 1) = a := rfl
  have ed : natModel.evalTerm
      (Structure.update natModel (Structure.update natModel env a) d)
      (Term.var 0) = d := rfl
  show natModel.evalFormula _
        (unpairGraph (shift2' N) (Term.var 1) (Term.var 0)) ⊗
      natModel.evalFormula _
        (betaGraph (Term.var 1) (Term.var 0) (shift2' I) (shift2' W)) = 1 ↔ _
  rw [conj_crisp_one_iff (unpairGraph_crisp' _ _ _ _)
      (betaGraph_crisp' _ _ _ _ _),
    unpairGraph_eval_one_iff', betaGraph_eval_one_iff',
    eN, eI, eW, ea, ed]

/-- The relational form of the node case matches the `CohereNat` node case: a
    triple `(a, b, p)` with `k = p+1` and `p = Nat.pair a b` exists with both
    children marked exactly when `k` is a node whose unpaired children of `k-1`
    are marked. -/
private theorem child_bridge (N k : Nat) :
    (∃ a b p : Nat, k = p + 1 ∧ p = Nat.pair a b ∧
        Nat.beta N a = 1 ∧ Nat.beta N b = 1) ↔
      (0 < k ∧ Nat.beta N (Nat.unpair (k - 1)).1 = 1 ∧
        Nat.beta N (Nat.unpair (k - 1)).2 = 1) := by
  constructor
  · rintro ⟨a, b, p, hk, hp, ha, hb⟩
    subst hk
    have hup : Nat.unpair (p + 1 - 1) = (a, b) := by
      rw [Nat.add_sub_cancel, hp, Nat.unpair_pair]
    rw [hup]
    exact ⟨Nat.succ_pos p, ha, hb⟩
  · rintro ⟨hpos, hb1, hb2⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [Nat.succ_sub_one] at hb1 hb2
    refine ⟨(Nat.unpair m).1, (Nat.unpair m).2, m, rfl, ?_, hb1, hb2⟩
    exact (Nat.pair_unpair m).symm

/-- `betaNF` evaluates crisply at every term tuple. -/
private theorem betaNF_crisp (env : natModel.Assignment) (N I W : ArithQTerm) :
    natModel.evalFormula env (betaNF N I W) = 0 ∨
      natModel.evalFormula env (betaNF N I W) = 1 := by
  rw [betaNF]
  exact existsE_crisp' _ _
    (fun a => existsE_crisp' _ _
      (fun d => conj_crisp (unpairGraph_crisp' _ _ _ _)
        (betaGraph_crisp' _ _ _ _ _)))

/-! ### The tree formula

`treeFormula x` asserts the course-of-values witness existentially and the
bounded coherence universally, exactly mirroring `isTree_iff_beta`. -/

/-- The node-case matrix under the three child binders `a := v 2`, `b := v 1`,
    `p := v 0`, with `k := v 3` and `N := v 4`. -/
private def treeChildBody : ArithQFormula :=
  .conj
    (.conj
      (.conj (.equal (v 3) (succT (v 0))) (pairGraph (v 2) (v 1) (v 0)))
      (betaNF (v 4) (v 2) oneT))
    (betaNF (v 4) (v 1) oneT)

/-- The node case: `∃ a b p, k = p+1 ∧ p = pair a b ∧ beta N a = 1 ∧
    beta N b = 1`, with `k := v 1`, `N := v 2` outside the three binders. -/
private def treeChild : ArithQFormula :=
  .existsE (.existsE (.existsE treeChildBody))

/-- Coherence at `k := v 0` (with `N := v 1`): `beta N k = 1` iff `k = 0` or the
    node case holds. -/
private def treeCoh : ArithQFormula :=
  iffF (betaNF (v 1) (v 0) oneT)
    (.disj (.equal (v 0) zeroT) treeChild)

/-- The node-case matrix is crisp at every witness assignment. -/
private theorem treeChildBody_crisp (e : natModel.Assignment) :
    natModel.evalFormula e treeChildBody = 0 ∨
      natModel.evalFormula e treeChildBody = 1 := by
  rw [treeChildBody]
  show ((natModel.evalFormula e (.equal (v 3) (succT (v 0))) ⊗
      natModel.evalFormula e (pairGraph (v 2) (v 1) (v 0))) ⊗
      natModel.evalFormula e (betaNF (v 4) (v 2) oneT)) ⊗
      natModel.evalFormula e (betaNF (v 4) (v 1) oneT) = 0 ∨ _
  exact conj_crisp
    (conj_crisp
      (conj_crisp (eqAtom_crisp _ _ _) (pairGraph_crisp' _ _ _ _))
      (betaNF_crisp _ _ _ _))
    (betaNF_crisp _ _ _ _)

/-- The node case `treeChild` evaluated at `e`: designated exactly when there is
    a triple `(a, b, p)` with `e 0 = p + 1`, `p = pair a b`, and both children
    marked under the table `e 1`. -/
private theorem treeChild_eval_one_iff (e : natModel.Assignment)
    (kv nv : Nat) (hk0 : e 0 = kv) (hn1 : e 1 = nv) :
    natModel.evalFormula e treeChild = 1 ↔
      (∃ a b p : Nat, kv = p + 1 ∧ p = Nat.pair a b ∧
        Nat.beta nv a = 1 ∧ Nat.beta nv b = 1) := by
  have hbInner : ∀ a b p : Nat,
      natModel.evalFormula
          (Structure.update natModel
            (Structure.update natModel (Structure.update natModel e a) b) p)
          treeChildBody = 1 ↔
        (kv = p + 1 ∧ p = Nat.pair a b ∧
          Nat.beta nv a = 1 ∧ Nat.beta nv b = 1) := by
    intro a b p
    set e4 := Structure.update natModel
      (Structure.update natModel (Structure.update natModel e a) b) p with he4
    -- variable readings at `e4`
    have v0 : natModel.evalTerm e4 (v 0) = p := rfl
    have v1 : natModel.evalTerm e4 (v 1) = b := rfl
    have v2 : natModel.evalTerm e4 (v 2) = a := rfl
    have v3 : natModel.evalTerm e4 (v 3) = kv := hk0
    have v4 : natModel.evalTerm e4 (v 4) = nv := hn1
    have vs0 : natModel.evalTerm e4 (succT (v 0)) = (p + 1 : Nat) := rfl
    have v1one : natModel.evalTerm e4 oneT = (1 : Nat) := rfl
    rw [treeChildBody]
    show ((natModel.evalFormula e4 (.equal (v 3) (succT (v 0))) ⊗
        natModel.evalFormula e4 (pairGraph (v 2) (v 1) (v 0))) ⊗
        natModel.evalFormula e4 (betaNF (v 4) (v 2) oneT)) ⊗
        natModel.evalFormula e4 (betaNF (v 4) (v 1) oneT) = 1 ↔ _
    rw [conj_crisp_one_iff
        (conj_crisp
          (conj_crisp (eqAtom_crisp _ _ _) (pairGraph_crisp' _ _ _ _))
          (betaNF_crisp _ _ _ _))
        (betaNF_crisp _ _ _ _),
      conj_crisp_one_iff
        (conj_crisp (eqAtom_crisp _ _ _) (pairGraph_crisp' _ _ _ _))
        (betaNF_crisp _ _ _ _),
      conj_crisp_one_iff (eqAtom_crisp _ _ _) (pairGraph_crisp' _ _ _ _),
      eqAtom_eval_one_iff, pairGraph_eval_one_iff,
      betaNF_eval_one_iff, betaNF_eval_one_iff,
      v0, v1, v2, v3, v4, vs0, v1one]
    show ((kv = p + 1 ∧ p = Nat.pair a b) ∧ (1 : Nat) = Nat.beta nv a) ∧
        (1 : Nat) = Nat.beta nv b ↔ _
    constructor
    · rintro ⟨⟨⟨hk, hp⟩, hba⟩, hbb⟩
      exact ⟨hk, hp, hba.symm, hbb.symm⟩
    · rintro ⟨hk, hp, hba, hbb⟩
      exact ⟨⟨⟨hk, hp⟩, hba.symm⟩, hbb.symm⟩
  -- peel the three existentials
  have hc3 : ∀ a b : Nat, ∀ p : Nat,
      natModel.evalFormula
          (Structure.update natModel
            (Structure.update natModel (Structure.update natModel e a) b) p)
          treeChildBody = 0 ∨
        natModel.evalFormula
          (Structure.update natModel
            (Structure.update natModel (Structure.update natModel e a) b) p)
          treeChildBody = 1 :=
    fun a b p => treeChildBody_crisp _
  have hc2 : ∀ a b : Nat,
      natModel.evalFormula
          (Structure.update natModel (Structure.update natModel e a) b)
          (.existsE treeChildBody) = 0 ∨
        natModel.evalFormula
          (Structure.update natModel (Structure.update natModel e a) b)
          (.existsE treeChildBody) = 1 :=
    fun a b => existsE_crisp' _ _ (hc3 a b)
  have hc1 : ∀ a : Nat,
      natModel.evalFormula (Structure.update natModel e a)
          (.existsE (.existsE treeChildBody)) = 0 ∨
        natModel.evalFormula (Structure.update natModel e a)
          (.existsE (.existsE treeChildBody)) = 1 :=
    fun a => existsE_crisp' _ _ (hc2 a)
  rw [treeChild, existsE_crisp_one_iff e _ hc1]
  refine exists_congr fun a => ?_
  rw [existsE_crisp_one_iff _ _ (hc2 a)]
  refine exists_congr fun b => ?_
  rw [existsE_crisp_one_iff _ _ (hc3 a b)]
  exact exists_congr fun p => hbInner a b p

/-- `treeChild` is crisp. -/
private theorem treeChild_crisp (e : natModel.Assignment) :
    natModel.evalFormula e treeChild = 0 ∨
      natModel.evalFormula e treeChild = 1 := by
  rw [treeChild]
  exact existsE_crisp' _ _
    (fun a => existsE_crisp' _ _
      (fun b => existsE_crisp' _ _ (fun p => treeChildBody_crisp _)))

/-- The full tree formula at the outer term `x`: a beta table `N` marks `x` and
    is coherent at every `k ≤ x`. -/
def treeFormula (x : ArithQTerm) : ArithQFormula :=
  .existsE
    (.conj
      (betaNF (v 0) (Term.rename Nat.succ x) oneT)
      (.forallE
        (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) x)) treeCoh)))

/-- `treeCoh` is crisp. -/
private theorem treeCoh_crisp (e : natModel.Assignment) :
    natModel.evalFormula e treeCoh = 0 ∨
      natModel.evalFormula e treeCoh = 1 := by
  rw [treeCoh]
  refine iffF_crisp e _ _ (betaNF_crisp _ _ _ _) ?_
  show natModel.evalFormula e (.equal (v 0) zeroT) ⊔
    natModel.evalFormula e treeChild = 0 ∨ _
  exact disj_crisp' (eqAtom_crisp _ _ _) (treeChild_crisp _)

/-- Coherence formula evaluated at `e`: designated exactly when the beta table
    `e 1` is coherent at index `e 0`. -/
private theorem treeCoh_eval_one_iff (e : natModel.Assignment)
    (kv nv : Nat) (hk0 : e 0 = kv) (hn1 : e 1 = nv) :
    natModel.evalFormula e treeCoh = 1 ↔ CohereNat nv kv := by
  have ev0 : natModel.evalTerm e (v 0) = kv := hk0
  have ev1 : natModel.evalTerm e (v 1) = nv := hn1
  have evone : natModel.evalTerm e oneT = (1 : Nat) := rfl
  have evzero : natModel.evalTerm e zeroT = (0 : Nat) := rfl
  -- the beta-marking side
  have hbeta : natModel.evalFormula e (betaNF (v 1) (v 0) oneT) = 1 ↔
      Nat.beta nv kv = 1 := by
    rw [betaNF_eval_one_iff, ev0, ev1, evone]
    exact eq_comm
  -- the disjunctive side: leaf or node case
  have hkzero : natModel.evalFormula e (.equal (v 0) zeroT) = 1 ↔ kv = 0 := by
    rw [eqAtom_eval_one_iff, ev0, evzero]
  have hdisj : natModel.evalFormula e
        (.disj (.equal (v 0) zeroT) treeChild) = 1 ↔
      (kv = 0 ∨ (0 < kv ∧ Nat.beta nv (Nat.unpair (kv - 1)).1 = 1 ∧
        Nat.beta nv (Nat.unpair (kv - 1)).2 = 1)) := by
    show natModel.evalFormula e (.equal (v 0) zeroT) ⊔
        natModel.evalFormula e treeChild = 1 ↔ _
    rw [disj_crisp_one_iff (eqAtom_crisp _ _ _) (treeChild_crisp _),
      hkzero, treeChild_eval_one_iff e kv nv hk0 hn1, child_bridge]
  have hdcrisp : natModel.evalFormula e
        (.disj (.equal (v 0) zeroT) treeChild) = 0 ∨
      natModel.evalFormula e (.disj (.equal (v 0) zeroT) treeChild) = 1 := by
    show natModel.evalFormula e (.equal (v 0) zeroT) ⊔
      natModel.evalFormula e treeChild = 0 ∨ _
    exact disj_crisp' (eqAtom_crisp _ _ _) (treeChild_crisp _)
  rw [treeCoh,
    iffF_eval_one_iff e _ _ (betaNF_crisp _ _ _ _) hdcrisp,
    hbeta, hdisj]
  rfl

/-- The renamed outer term evaluates to its value past the binders it crosses. -/
private theorem eval_rename_numeral (env : natModel.Assignment) (ρ : Nat → Nat)
    (n : Nat) (e : natModel.Assignment) (he : e = fun k => env (ρ k)) :
    natModel.evalTerm env (Term.rename ρ (numeral n)) = n := by
  rw [Structure.evalTerm_rename, ← he, eval_numeral]

/-- The bounded-coherence body evaluated at `e` (with `e 0 = kv`, `e 1 = nv`):
    designated iff `kv ≤ x` implies coherence at `kv`. -/
private theorem cohBody_eval_one_iff (env : natModel.Assignment) (n : Nat)
    (nv : Nat) (kv : Nat) :
    natModel.evalFormula
        (Structure.update natModel (Structure.update natModel env nv) kv)
        (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
          treeCoh) = 1 ↔
      (kv ≤ n → CohereNat nv kv) := by
  set e1 := Structure.update natModel (Structure.update natModel env nv) kv
    with he1
  have hle : natModel.evalFormula e1
        (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n))) = 1 ↔
      kv ≤ n := by
    rw [leF_eval_one_iff]
    have hx : natModel.evalTerm e1
        (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)) = n :=
      eval_rename_numeral e1 (Nat.succ ∘ Nat.succ) n env (by
        funext k; rfl)
    have hv0 : natModel.evalTerm e1 (v 0) = kv := rfl
    rw [hx, hv0]
  have hcoh : natModel.evalFormula e1 treeCoh = 1 ↔ CohereNat nv kv :=
    treeCoh_eval_one_iff e1 kv nv rfl rfl
  have hlecrisp : natModel.evalFormula e1
      (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n))) = 0 ∨
    natModel.evalFormula e1
      (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n))) = 1 :=
    leF_crisp _ _ _
  rw [impF_eval_one_iff e1 _ _ hlecrisp (treeCoh_crisp _), hle, hcoh]

/-- Object-language bridge: the tree formula at `numeral n` is designated exactly
    when there is a coherent beta table marking `n`. -/
theorem treeFormula_eval_one_iff (n : Nat) (env : natModel.Assignment) :
    natModel.evalFormula env (treeFormula (numeral n)) = 1 ↔
      ∃ N : Nat, Nat.beta N n = 1 ∧ ∀ k, k ≤ n → CohereNat N k := by
  -- the matrix under the `∃ N` binder, at witness `nv`
  have hmatrix : ∀ nv : Nat,
      natModel.evalFormula (Structure.update natModel env nv)
          (.conj (betaNF (v 0) (Term.rename Nat.succ (numeral n)) oneT)
            (.forallE
              (impF
                (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
                treeCoh))) = 1 ↔
        (Nat.beta nv n = 1 ∧ ∀ k, k ≤ n → CohereNat nv k) := by
    intro nv
    set e0 := Structure.update natModel env nv with he0
    -- left conjunct: the table marks `n`
    have hleft : natModel.evalFormula e0
          (betaNF (v 0) (Term.rename Nat.succ (numeral n)) oneT) = 1 ↔
        Nat.beta nv n = 1 := by
      rw [betaNF_eval_one_iff]
      have hx : natModel.evalTerm e0 (Term.rename Nat.succ (numeral n)) = n :=
        eval_rename_numeral e0 Nat.succ n env (by funext k; rfl)
      have hv0 : natModel.evalTerm e0 (v 0) = nv := rfl
      have hone : natModel.evalTerm e0 oneT = (1 : Nat) := rfl
      rw [hx, hv0, hone]
      exact eq_comm
    -- right conjunct: bounded coherence
    have hright : natModel.evalFormula e0
          (.forallE
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh)) = 1 ↔
        (∀ k, k ≤ n → CohereNat nv k) := by
      show natModel.all (fun kv =>
          natModel.evalFormula (Structure.update natModel e0 kv)
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh)) = 1 ↔ _
      have hbcrisp : ∀ kv : Nat,
          natModel.evalFormula (Structure.update natModel e0 kv)
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh) = 0 ∨
          natModel.evalFormula (Structure.update natModel e0 kv)
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh) = 1 :=
        fun kv => impF_crisp _ _ _ (leF_crisp _ _ _) (treeCoh_crisp _)
      exact (crisp_all_one_iff _ hbcrisp).trans
        (forall_congr' fun kv => cohBody_eval_one_iff env n nv kv)
    -- assemble the conjunction
    have hlcrisp : natModel.evalFormula e0
          (betaNF (v 0) (Term.rename Nat.succ (numeral n)) oneT) = 0 ∨
        natModel.evalFormula e0
          (betaNF (v 0) (Term.rename Nat.succ (numeral n)) oneT) = 1 :=
      betaNF_crisp _ _ _ _
    have hrcrisp : natModel.evalFormula e0
          (.forallE
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh)) = 0 ∨
        natModel.evalFormula e0
          (.forallE
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh)) = 1 := by
      show natModel.all (fun kv =>
          natModel.evalFormula (Structure.update natModel e0 kv)
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh)) = 0 ∨ _
      exact crisp_all_crisp _
        (fun kv => impF_crisp _ _ _ (leF_crisp _ _ _) (treeCoh_crisp _))
    show natModel.evalFormula e0
          (betaNF (v 0) (Term.rename Nat.succ (numeral n)) oneT) ⊗
        natModel.evalFormula e0
          (.forallE
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh)) = 1 ↔ _
    rw [conj_crisp_one_iff hlcrisp hrcrisp, hleft, hright]
  -- peel the outer existential
  have hcrisp : ∀ nv : Nat,
      natModel.evalFormula (Structure.update natModel env nv)
          (.conj (betaNF (v 0) (Term.rename Nat.succ (numeral n)) oneT)
            (.forallE
              (impF
                (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
                treeCoh))) = 0 ∨
        natModel.evalFormula (Structure.update natModel env nv)
          (.conj (betaNF (v 0) (Term.rename Nat.succ (numeral n)) oneT)
            (.forallE
              (impF
                (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
                treeCoh))) = 1 := by
    intro nv
    show natModel.evalFormula (Structure.update natModel env nv)
          (betaNF (v 0) (Term.rename Nat.succ (numeral n)) oneT) ⊗
        natModel.evalFormula (Structure.update natModel env nv)
          (.forallE
            (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
              treeCoh)) = 0 ∨ _
    refine conj_crisp (betaNF_crisp _ _ _ _) ?_
    show natModel.all (fun kv =>
        natModel.evalFormula
          (Structure.update natModel (Structure.update natModel env nv) kv)
          (impF (leF (v 0) (Term.rename (Nat.succ ∘ Nat.succ) (numeral n)))
            treeCoh)) = 0 ∨ _
    exact crisp_all_crisp _
      (fun kv => impF_crisp _ _ _ (leF_crisp _ _ _) (treeCoh_crisp _))
  rw [treeFormula, existsE_crisp_one_iff env _ hcrisp]
  exact exists_congr hmatrix

/-- The object-language tree formula represents the recursive tree predicate in
    the standard model: `treeFormula (numeral n)` is designated exactly when `n`
    codes a binary tree. -/
theorem treeFormula_represents (n : Nat) (env : natModel.Assignment) :
    natModel.evalFormula env (treeFormula (numeral n)) = 1 ↔ isTree n = true :=
  (treeFormula_eval_one_iff n env).trans (isTree_iff_beta n).symm

end arithQ
