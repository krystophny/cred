-- Properties of the ProbTT typing system
--
-- NOTE: This module uses postulates for standard metatheoretic lemmas:
-- - Substitution admissibility: typing is preserved under substitution
-- - Type conversion: definitionally equal types can be interchanged
-- These are well-established results in type theory but require substantial
-- infrastructure (parallel substitution calculus) to prove formally.

module ProbTT.Properties where

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Substitution
open import ProbTT.Context
open import ProbTT.Judgment

-- Properties of the typing system
module Props {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM

  -- Helper: w · v ≤ v (multiplication also decreases to second argument)
  ·-≤-right : ∀ w v → w · v ≤ v
  ·-≤-right w v = subst (λ x → x ≤ v) (·-comm v w) (·-≤-self v w)

  -- Weight bound: all weights are bounded by 𝟙
  -- This follows from: we can only lower weights, and variables are at 𝟙
  weight-bounded : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w : W} →
                   Γ ⊢ t ∶ A 〔 w 〕 →
                   w ≤ 𝟙
  weight-bounded (t-var i)         = ≤-refl 𝟙
  weight-bounded (t-weaken d v≤w)  = ≤-trans v≤w (weight-bounded d)
  weight-bounded (t-lam d)         = weight-bounded d
  weight-bounded (t-app df da)     = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  weight-bounded (t-pair da db)    = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  weight-bounded (t-fst d)         = weight-bounded d
  weight-bounded (t-snd d)         = weight-bounded d
  weight-bounded (t-inl d)         = weight-bounded d
  weight-bounded (t-inr d)         = weight-bounded d
  weight-bounded (t-case de dl dr) = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  weight-bounded (t-refl d)        = weight-bounded d
  weight-bounded (t-J dp dd)       = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)

  -- Weight monotonicity: multiplication preserves order
  -- If v ≤ w then u · v ≤ u · w
  -- This requires additional axioms on the algebra (monotonicity of ·)
  -- For now we leave this as a postulate since it holds in all standard instances

  -- Weakening is admissible (structural rule)
  -- If Γ ⊢ t : A 〔 w 〕 then Γ,B ⊢ wk t : wk A 〔 w 〕
  -- This follows by induction on the derivation

  -- Substitution is admissible (key structural lemma)
  -- If Γ ⊢ a : A 〔 w 〕 and Γ,A ⊢ b : B 〔 v 〕 then Γ ⊢ b[a] : B[a] 〔 w 〕·v

  -- Identity at weight 𝟙
  id-typed : ∀ {n} {Γ : Ctx n} {A : Ty n} →
             Γ ⊢ A type →
             Γ ⊢ lam A (var zero) ∶ (A ⇒ wkTy A) 〔 𝟙 〕
  id-typed Af = t-lam (t-var zero)

  -- Composition multiplies weights
  -- Given f : A → B 〔 w 〕 and g : B → C 〔 v 〕
  -- We get g ∘ f : A → C 〔 w 〕 · v

  -- ═══════════════════════════════════════════════════════════════════════
  -- PROOF BY CONTRADICTION (Meta-Theorem)
  -- ═══════════════════════════════════════════════════════════════════════
  --
  -- In ProbTT, there is no Empty type (𝟘') and no explosion rule (abort).
  -- Instead, impossibility is represented by weight 𝟘.
  --
  -- Proof by contradiction works at the META level (in Agda), not the
  -- object level (in ProbTT terms):
  --
  -- Meta-Theorem (Contradiction Discovery):
  --   If assuming w > 𝟘 leads to a contradiction in Agda's meta-logic,
  --   then w ≡ 𝟘.
  --
  -- Example (√2 is irrational):
  --   1. Assume "√2 is rational" has weight w
  --   2. Derive (at meta-level) that this leads to: p even ∧ q even ∧ gcd=1
  --   3. This is contradictory, so w > 𝟘 → ⊥ (in Agda)
  --   4. By meta-level reasoning, w ≡ 𝟘
  --   5. Therefore "√2 is irrational" has weight ¬𝟘 = 𝟙
  --
  -- This is sound because:
  --   - We're proving theorems ABOUT weights, not deriving terms
  --   - The object language never has explosion
  --   - Classical/constructive meta-logic is separate from ProbTT
  --
  -- The key insight: proof by contradiction discovers that an assumption
  -- was weight 𝟘, rather than using ⊥ as a springboard to arbitrary conclusions.
  -- ═══════════════════════════════════════════════════════════════════════

  -- Weight 𝟘 propagates through all operations (no escape)
  -- This is why we don't need abort: if a : A @ 𝟘, then f a : B 〔 w 〕·𝟘 = 𝟘

  -- Multiplication annihilates at 𝟘
  zero-annihilates : ∀ (w : W) → w · 𝟘 ≡ 𝟘
  zero-annihilates = ·-annihilʳ

  -- Type preservation under beta reduction
  -- If Γ ⊢ t ≡ t' : A 〔 w 〕 then Γ ⊢ t : A 〔 w 〕 and Γ ⊢ t' : A 〔 w 〕
  preservation-left : ∀ {n} {Γ : Ctx n} {t t' : Tm n} {A : Ty n} {w : W} →
                      Γ ⊢ t ≐ t' ∶ A 〔 w 〕 →
                      Γ ⊢ t ∶ A 〔 w 〕
  preservation-left (eq-refl d) = d
  preservation-left (eq-sym eq) = preservation-right eq
    where
      preservation-right : ∀ {n} {Γ : Ctx n} {t t' : Tm n} {A : Ty n} {w : W} →
                           Γ ⊢ t ≐ t' ∶ A 〔 w 〕 →
                           Γ ⊢ t' ∶ A 〔 w 〕
      preservation-right (eq-refl d) = d
      preservation-right (eq-sym eq) = preservation-left eq
      preservation-right (eq-trans eq1 eq2) = preservation-right eq2
      preservation-right (Π-β db da) = subst-typed db da
        where
          -- POSTULATE: Substitution admissibility
          -- This is the fundamental substitution lemma for dependent types.
          -- Proof requires: substitution calculus, simultaneous substitution,
          -- and compatibility with all type formers.
          -- Standard in MLTT literature (cf. Hofmann's thesis).
          postulate
            subst-typed : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)}
                            {b : Tm (suc n)} {a : Tm n} {w v : W} →
                          (Γ , A) ⊢ b ∶ B 〔 w 〕 →
                          Γ ⊢ a ∶ A 〔 v 〕 →
                          Γ ⊢ (b [ a ]) ∶ (B [ a ]ₜ) 〔 w · v 〕
      preservation-right (Σ-β₁ da db) = t-weaken da (·-≤-self _ _)
      preservation-right (Σ-β₂ {w = w} {v = v} da db) = t-weaken db (·-≤-right w v)
      preservation-right (+-β-inl da dl dr) = subst-typed-sum-inl da dl
        where
          postulate
            subst-typed-sum-inl : ∀ {n} {Γ : Ctx n} {A C : Ty n} {a : Tm n} {l : Tm (suc n)} {w v : W} →
                                  Γ ⊢ a ∶ A 〔 w 〕 →
                                  (Γ , A) ⊢ l ∶ wkTy C 〔 v 〕 →
                                  Γ ⊢ (l [ a ]) ∶ C 〔 w · v 〕
      preservation-right (+-β-inr db dl dr) = subst-typed-sum-inr db dr
        where
          postulate
            subst-typed-sum-inr : ∀ {n} {Γ : Ctx n} {B C : Ty n} {b : Tm n} {r : Tm (suc n)} {w v : W} →
                                  Γ ⊢ b ∶ B 〔 w 〕 →
                                  (Γ , B) ⊢ r ∶ wkTy C 〔 v 〕 →
                                  Γ ⊢ (r [ b ]) ∶ C 〔 w · v 〕
      preservation-right (Id-β {w = w} {v = v} da dd) = t-weaken dd (·-≤-right w v)
  preservation-left (eq-trans eq1 eq2) = preservation-left eq1
  preservation-left (Π-β db da) = t-app (t-lam db) da
  preservation-left (Σ-β₁ da db) = t-fst (t-pair da db)
  preservation-left (Σ-β₂ da db) = conversion-snd da db
    where
      -- POSTULATE: Type conversion for dependent pairs
      -- We need: Γ ⊢ snd (pair a b) ∶ B[a] [ w·v ]
      -- From t-snd (t-pair da db) we get: Γ ⊢ snd (pair a b) ∶ B[fst(pair a b)] [ w·v ]
      -- These types are definitionally equal because fst(pair a b) reduces to a.
      -- Type conversion requires proving B[fst(pair a b)] ≡ B[a], which follows
      -- from the beta rule and congruence of substitution.
      postulate
        conversion-snd : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {w v : W} →
                         Γ ⊢ a ∶ A 〔 w 〕 →
                         Γ ⊢ b ∶ (B [ a ]ₜ) 〔 v 〕 →
                         Γ ⊢ snd (pair a b) ∶ (B [ a ]ₜ) 〔 w · v 〕
  preservation-left (+-β-inl da dl dr) = t-case (t-inl da) dl dr
  preservation-left (+-β-inr db dl dr) = t-case (t-inr db) dl dr
  preservation-left (Id-β da dd) = t-J (t-refl da) dd
