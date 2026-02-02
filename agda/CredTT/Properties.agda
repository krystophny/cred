{- AXIOM STATUS SUMMARY for Properties.agda

subst-typed, subst-typed-sum-*: SHOULD BE PROVEN (Issues #115, #118)
  Fundamental substitution lemma for dependent types.
  Requires parallel substitution calculus, simultaneous substitution,
  and compatibility with all type formers.
  Reference: Hofmann thesis, Harper PFPL, PLFA "Properties"
  See GitHub issues #115, #118 for tracking.

conversion-snd: SHOULD BE PROVEN
  Type conversion using definitional equality B[fst(pair a b)] = B[a].
  Requires congruence of substitution under beta.

These are NOT fundamental axioms but FORMALIZATION GAPS to be filled.
The postulates are standard metatheoretic results (proven in literature).
-}
-- Properties of the CredTT typing system
--
-- NOTE: This module uses postulates for standard metatheoretic lemmas:
-- - Substitution admissibility: typing is preserved under substitution
-- - Type conversion: definitionally equal types can be interchanged
-- These are well-established results in type theory but require substantial
-- infrastructure (parallel substitution calculus) to prove formally.

module CredTT.Properties where

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import CredTT.Credence
open import CredTT.Syntax
open import CredTT.Substitution
open import CredTT.Context
open import CredTT.Judgment

-- Properties of the typing system
module Props {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM

  -- Helper: c . d <= d (multiplication also decreases to second argument)
  ·-≤-right : ∀ c d → c · d ≤ d
  ·-≤-right c d = subst (λ x → x ≤ d) (·-comm d c) (·-≤-self d c)

  -- Credence bound: all credences are bounded by 1
  -- This follows from: we can only lower credences, and variables are at 1
  credence-bounded : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c : C} →
                     Γ ⊢ t ∶ A 〔 c 〕 →
                     c ≤ 𝟙
  credence-bounded (t-var i)         = ≤-refl 𝟙
  credence-bounded (t-weaken d d≤c)  = ≤-trans d≤c (credence-bounded d)
  credence-bounded (t-lam d)         = credence-bounded d
  credence-bounded (t-app df da)     = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  credence-bounded (t-pair da db)    = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  credence-bounded (t-fst d)         = credence-bounded d
  credence-bounded (t-snd d)         = credence-bounded d
  credence-bounded (t-inl d)         = credence-bounded d
  credence-bounded (t-inr d)         = credence-bounded d
  credence-bounded (t-case de dl dr) = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  credence-bounded (t-refl d)        = credence-bounded d
  credence-bounded (t-J dp dd)       = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)

  -- Credence monotonicity: multiplication preserves order
  -- If d <= c then e . d <= e . c
  -- This requires additional axioms on the algebra (monotonicity of .)
  -- For now we leave this as a postulate since it holds in all standard instances

  -- Weakening is admissible (structural rule)
  -- If Gamma |- t : A [ c ] then Gamma,B |- wk t : wk A [ c ]
  -- This follows by induction on the derivation

  -- Substitution is admissible (key structural lemma)
  -- If Gamma |- a : A [ c ] and Gamma,A |- b : B [ d ] then Gamma |- b[a] : B[a] [ c.d ]

  -- Identity at credence 1
  id-typed : ∀ {n} {Γ : Ctx n} {A : Ty n} →
             Γ ⊢ A type →
             Γ ⊢ lam A (var zero) ∶ (A ⇒ wkTy A) 〔 𝟙 〕
  id-typed Af = t-lam (t-var zero)

  -- Composition multiplies credences
  -- Given f : A -> B [ c ] and g : B -> C [ d ]
  -- We get g o f : A -> C [ c . d ]

  -- ===================================================================
  -- PROOF BY CONTRADICTION (Meta-Theorem)
  -- ===================================================================
  --
  -- In CredTT, there is no Empty type (Zero') and no explosion rule (abort).
  -- Instead, impossibility is represented by credence 0.
  --
  -- Proof by contradiction works at the META level (in Agda), not the
  -- object level (in CredTT terms):
  --
  -- Meta-Theorem (Contradiction Discovery):
  --   If assuming c > 0 leads to a contradiction in Agda's meta-logic,
  --   then c = 0.
  --
  -- Example (sqrt(2) is irrational):
  --   1. Assume "sqrt(2) is rational" has credence c
  --   2. Derive (at meta-level) that this leads to: p even and q even and gcd=1
  --   3. This is contradictory, so c > 0 -> bot (in Agda)
  --   4. By meta-level reasoning, c = 0
  --   5. Therefore "sqrt(2) is irrational" has credence neg 0 = 1
  --
  -- This is sound because:
  --   - We're proving theorems ABOUT credences, not deriving terms
  --   - The object language never has explosion
  --   - Classical/constructive meta-logic is separate from CredTT
  --
  -- The key insight: proof by contradiction discovers that an assumption
  -- was credence 0, rather than using bot as a springboard to arbitrary conclusions.
  -- ===================================================================

  -- Credence 0 propagates through all operations (no escape)
  -- This is why we don't need abort: if a : A @ 0, then f a : B [ c.0 ] = 0

  -- Multiplication annihilates at 0
  zero-annihilates : ∀ (c : C) → c · 𝟘 ≡ 𝟘
  zero-annihilates = ·-annihilʳ

  -- Type preservation under beta reduction
  -- If Gamma |- t = t' : A [ c ] then Gamma |- t : A [ c ] and Gamma |- t' : A [ c ]
  preservation-left : ∀ {n} {Γ : Ctx n} {t t' : Tm n} {A : Ty n} {c : C} →
                      Γ ⊢ t ≐ t' ∶ A 〔 c 〕 →
                      Γ ⊢ t ∶ A 〔 c 〕
  preservation-left (eq-refl d) = d
  preservation-left (eq-sym eq) = preservation-right eq
    where
      preservation-right : ∀ {n} {Γ : Ctx n} {t t' : Tm n} {A : Ty n} {c : C} →
                           Γ ⊢ t ≐ t' ∶ A 〔 c 〕 →
                           Γ ⊢ t' ∶ A 〔 c 〕
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
                            {b : Tm (suc n)} {a : Tm n} {c d : C} →
                          (Γ , A) ⊢ b ∶ B 〔 c 〕 →
                          Γ ⊢ a ∶ A 〔 d 〕 →
                          Γ ⊢ (b [ a ]) ∶ (B [ a ]ₜ) 〔 c · d 〕
      preservation-right (Σ-β₁ da db) = t-weaken da (·-≤-self _ _)
      preservation-right (Σ-β₂ {c = c} {d = d} da db) = t-weaken db (·-≤-right c d)
      preservation-right (+-β-inl da dl dr) = subst-typed-sum-inl da dl
        where
          postulate
            subst-typed-sum-inl : ∀ {n} {Γ : Ctx n} {A D : Ty n} {a : Tm n} {l : Tm (suc n)} {c d : C} →
                                  Γ ⊢ a ∶ A 〔 c 〕 →
                                  (Γ , A) ⊢ l ∶ wkTy D 〔 d 〕 →
                                  Γ ⊢ (l [ a ]) ∶ D 〔 c · d 〕
      preservation-right (+-β-inr db dl dr) = subst-typed-sum-inr db dr
        where
          postulate
            subst-typed-sum-inr : ∀ {n} {Γ : Ctx n} {B D : Ty n} {b : Tm n} {r : Tm (suc n)} {c d : C} →
                                  Γ ⊢ b ∶ B 〔 c 〕 →
                                  (Γ , B) ⊢ r ∶ wkTy D 〔 d 〕 →
                                  Γ ⊢ (r [ b ]) ∶ D 〔 c · d 〕
      preservation-right (Id-β {c = c} {e = e} da dd) = t-weaken dd (·-≤-right c e)
  preservation-left (eq-trans eq1 eq2) = preservation-left eq1
  preservation-left (Π-β db da) = t-app (t-lam db) da
  preservation-left (Σ-β₁ da db) = t-fst (t-pair da db)
  preservation-left (Σ-β₂ da db) = conversion-snd da db
    where
      -- POSTULATE: Type conversion for dependent pairs
      -- We need: Gamma |- snd (pair a b) : B[a] [ c.d ]
      -- From t-snd (t-pair da db) we get: Gamma |- snd (pair a b) : B[fst(pair a b)] [ c.d ]
      -- These types are definitionally equal because fst(pair a b) reduces to a.
      -- Type conversion requires proving B[fst(pair a b)] = B[a], which follows
      -- from the beta rule and congruence of substitution.
      postulate
        conversion-snd : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {c d : C} →
                         Γ ⊢ a ∶ A 〔 c 〕 →
                         Γ ⊢ b ∶ (B [ a ]ₜ) 〔 d 〕 →
                         Γ ⊢ snd (pair a b) ∶ (B [ a ]ₜ) 〔 c · d 〕
  preservation-left (+-β-inl da dl dr) = t-case (t-inl da) dl dr
  preservation-left (+-β-inr db dl dr) = t-case (t-inr db) dl dr
  preservation-left (Id-β da dd) = t-J (t-refl da) dd
