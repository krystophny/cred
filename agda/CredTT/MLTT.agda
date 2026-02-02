module CredTT.MLTT where

open import Level using (Level; 0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import CredTT.Credence
open import CredTT.Syntax
open import CredTT.Substitution
open import CredTT.Context
open import CredTT.Judgment

-- =========================================================================
-- MLTT Fragment Embedding
-- =========================================================================
--
-- Pure CredTT is the fragment of MLTT with:
--   - Pi-types (dependent functions)
--   - Sigma-types (dependent pairs)
--   - +-types (coproducts/sums)
--   - Id-types (identity/equality)
--
-- NOT included in pure CredTT:
--   - Unit type (One): Certainty is credence 1 on any type, not a special type
--   - Empty type (Zero): Impossibility is credence 0 on any type, not a special type
--
-- Full MLTT with Unit and Empty would require extending CredTT's syntax.
-- The key insight: Pure CredTT avoids the philosophical question
-- "what TYPE is credence 0/1?" by using credences directly.
-- =========================================================================

open BoolDM

-- Import CredTT typing with Boolean credences
open Typing BoolDM

-- Standard MLTT typing (no credences) - fragment without Unit/Empty
-- This is the target of the embedding
data _⊢mltt_∶_ : ∀ {n} → Ctx n → Tm n → Ty n → Set where
  -- Variable
  mltt-var : ∀ {n} {Γ : Ctx n} (i : Fin n) →
             Γ ⊢mltt var i ∶ lookup Γ i

  -- Pi-Intro
  mltt-lam : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {b : Tm (suc n)} →
             (Γ , A) ⊢mltt b ∶ B →
             Γ ⊢mltt lam A b ∶ (A ⇒ B)

  -- Pi-Elim
  mltt-app : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {f a : Tm n} →
             Γ ⊢mltt f ∶ (A ⇒ B) →
             Γ ⊢mltt a ∶ A →
             Γ ⊢mltt app f a ∶ (B [ a ]ₜ)

  -- Sigma-Intro
  mltt-pair : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} →
              Γ ⊢mltt a ∶ A →
              Γ ⊢mltt b ∶ (B [ a ]ₜ) →
              Γ ⊢mltt pair a b ∶ (A ×' B)

  -- Sigma-Elim
  mltt-fst : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {t : Tm n} →
             Γ ⊢mltt t ∶ (A ×' B) →
             Γ ⊢mltt fst t ∶ A

  mltt-snd : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {t : Tm n} →
             Γ ⊢mltt t ∶ (A ×' B) →
             Γ ⊢mltt snd t ∶ (B [ fst t ]ₜ)

  -- +-Intro
  mltt-inl : ∀ {n} {Γ : Ctx n} {A B : Ty n} {a : Tm n} →
             Γ ⊢mltt a ∶ A →
             Γ ⊢mltt inl a ∶ (A +' B)

  mltt-inr : ∀ {n} {Γ : Ctx n} {A B : Ty n} {b : Tm n} →
             Γ ⊢mltt b ∶ B →
             Γ ⊢mltt inr b ∶ (A +' B)

  -- +-Elim
  mltt-case : ∀ {n} {Γ : Ctx n} {A B D : Ty n} {e : Tm n} {l r : Tm (suc n)} →
              Γ ⊢mltt e ∶ (A +' B) →
              (Γ , A) ⊢mltt l ∶ wkTy D →
              (Γ , B) ⊢mltt r ∶ wkTy D →
              Γ ⊢mltt case e l r ∶ D

  -- Id-Intro
  mltt-refl : ∀ {n} {Γ : Ctx n} {A : Ty n} {a : Tm n} →
              Γ ⊢mltt a ∶ A →
              Γ ⊢mltt refl' ∶ Id A a a

  -- Id-Elim
  mltt-J : ∀ {n} {Γ : Ctx n} {A : Ty n} {a b : Tm n}
             {M : Ty (suc (suc n))} {d p : Tm n} →
           Γ ⊢mltt p ∶ Id A a b →
           Γ ⊢mltt d ∶ (M [ refl' , a ]₂ₜ) →
           Γ ⊢mltt J M d p ∶ (M [ p , b ]₂ₜ)

-- Key fact: true . true = true in Boolean algebra
-- This means credences compose trivially at credence 1
∧-true-true : true ∧B true ≡ true
∧-true-true = refl

-- Helper for credence substitution
subst-credence : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c c' : Bool} →
                 Γ ⊢ t ∶ A 〔 c 〕 →
                 c ≡ c' →
                 Γ ⊢ t ∶ A 〔 c' 〕
subst-credence d refl = d

-- Embedding: MLTT -> CredTT [ true ]
-- An MLTT judgment becomes a CredTT judgment at credence 1
embed : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} →
        Γ ⊢mltt t ∶ A →
        Γ ⊢ t ∶ A 〔 true 〕
embed (mltt-var i) = t-var i
embed (mltt-lam d) = t-lam (embed d)
embed (mltt-app df da) = subst-credence (t-app (embed df) (embed da)) ∧-true-true
embed (mltt-pair da db) = subst-credence (t-pair (embed da) (embed db)) ∧-true-true
embed (mltt-fst d) = t-fst (embed d)
embed (mltt-snd d) = t-snd (embed d)
embed (mltt-inl d) = t-inl (embed d)
embed (mltt-inr d) = t-inr (embed d)
embed (mltt-case de dl dr) = subst-credence (t-case (embed de) (embed dl) (embed dr)) ∧-true-true
embed (mltt-refl d) = t-refl (embed d)
embed (mltt-J dp dd) = subst-credence (t-J (embed dp) (embed dd)) ∧-true-true

-- Lemma: if c and d = true then c = true and d = true
∧-true-inv : ∀ {c d} → c ∧B d ≡ true → c ≡ true
∧-true-inv {true} {true} refl = refl

∧-true-inv-right : ∀ {c d} → c ∧B d ≡ true → d ≡ true
∧-true-inv-right {true} {true} refl = refl

-- Helper to transport typing judgment along credence equality
transport-credence : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c c' : Bool} →
                     Γ ⊢ t ∶ A 〔 c 〕 → c ≡ c' → Γ ⊢ t ∶ A 〔 c' 〕
transport-credence d refl = d

-- Collapse: CredTT [ true ] -> MLTT
-- A CredTT judgment at credence 1 gives an MLTT judgment
-- We use mutual recursion with an explicit credence parameter
mutual
  collapse : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} →
             Γ ⊢ t ∶ A 〔 true 〕 →
             Γ ⊢mltt t ∶ A
  collapse d = collapse' d refl

  collapse' : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c : Bool} →
              Γ ⊢ t ∶ A 〔 c 〕 → c ≡ true →
              Γ ⊢mltt t ∶ A
  collapse' (t-var i) refl = mltt-var i
  collapse' (t-weaken d ≤-true) refl = collapse' d refl
  collapse' (t-lam d) refl = mltt-lam (collapse' d refl)
  collapse' (t-app {c = true} {d = true} df da) refl =
    mltt-app (collapse' df refl) (collapse' da refl)
  collapse' (t-pair {c = true} {d = true} da db) refl =
    mltt-pair (collapse' da refl) (collapse' db refl)
  collapse' (t-fst d) refl = mltt-fst (collapse' d refl)
  collapse' (t-snd d) refl = mltt-snd (collapse' d refl)
  collapse' (t-inl d) refl = mltt-inl (collapse' d refl)
  collapse' (t-inr d) refl = mltt-inr (collapse' d refl)
  collapse' (t-case {c = true} {d = true} de dl dr) refl =
    mltt-case (collapse' de refl) (collapse' dl refl) (collapse' dr refl)
  collapse' (t-refl d) refl = mltt-refl (collapse' d refl)
  collapse' (t-J {c = true} {e = true} dp dd) refl =
    mltt-J (collapse' dp refl) (collapse' dd refl)

-- Round-trip: embed then collapse is identity
embed-collapse : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n}
                   (d : Γ ⊢mltt t ∶ A) →
                 collapse (embed d) ≡ d
embed-collapse (mltt-var i) = refl
embed-collapse (mltt-lam d) = cong mltt-lam (embed-collapse d)
embed-collapse (mltt-app df da) = cong₂ mltt-app (embed-collapse df) (embed-collapse da)
  where
    cong₂ : ∀ {A B D : Set} (f : A → B → D) {x₁ x₂ : A} {y₁ y₂ : B} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
    cong₂ f refl refl = refl
embed-collapse (mltt-pair da db) = cong₂ mltt-pair (embed-collapse da) (embed-collapse db)
  where
    cong₂ : ∀ {A B D : Set} (f : A → B → D) {x₁ x₂ : A} {y₁ y₂ : B} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
    cong₂ f refl refl = refl
embed-collapse (mltt-fst d) = cong mltt-fst (embed-collapse d)
embed-collapse (mltt-snd d) = cong mltt-snd (embed-collapse d)
embed-collapse (mltt-inl d) = cong mltt-inl (embed-collapse d)
embed-collapse (mltt-inr d) = cong mltt-inr (embed-collapse d)
embed-collapse (mltt-case de dl dr) = cong₃ mltt-case (embed-collapse de) (embed-collapse dl) (embed-collapse dr)
embed-collapse (mltt-refl d) = cong mltt-refl (embed-collapse d)
embed-collapse (mltt-J dp dd) = cong₂ mltt-J (embed-collapse dp) (embed-collapse dd)
  where
    cong₂ : ∀ {A B D : Set} (f : A → B → D) {x₁ x₂ : A} {y₁ y₂ : B} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
    cong₂ f refl refl = refl

-- =========================================================================
-- FORMALIZATION STATUS (Issue #76)
-- =========================================================================
--
-- PROVEN:
--   - embed : MLTT -> CredTT[true]
--   - collapse : CredTT[true] -> MLTT
--   - embed-collapse : collapse (embed d) ≡ d
--
-- NOT YET PROVEN:
--   - collapse-embed : embed (collapse d) ≡ d
--     This second round-trip is needed for a full isomorphism.
--     The difficulty is that CredTT derivations may have multiple
--     forms (e.g., t-weaken), so collapse loses structure.
--
-- CLAIM: The embedding is a one-sided comparison (MLTT embeds into CredTT).
--        Full isomorphism would require collapse-embed.
-- =========================================================================

-- =========================================================================
-- Note on Full MLTT
-- =========================================================================
--
-- Full MLTT includes Unit (One) and Empty (Zero) types with:
--   - One-Intro: star : One
--   - Zero-Elim: If e : Zero then abort A e : A (explosion principle)
--
-- In pure CredTT, we intentionally omit these because:
--   1. Certainty is credence 1 on any type, not a special Unit type
--   2. Impossibility is credence 0 on any type, not a special Empty type
--   3. This avoids "what TYPE is credence 0/1?" - a philosophical issue
--
-- GRADED EX FALSO works without Empty type:
--   If a : A @ 0, then f a : B [ c.0 ] = 0 automatically.
--   Credence 0 propagates through all operations. No explosion needed.
--
-- To embed full MLTT with Unit/Empty, one would need to extend
-- CredTT's syntax to include these types and their typing rules.
-- =========================================================================
