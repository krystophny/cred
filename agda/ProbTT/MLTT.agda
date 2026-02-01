module ProbTT.MLTT where

open import Level using (Level; 0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Substitution
open import ProbTT.Context
open import ProbTT.Judgment

-- MLTT is ProbTT with W = {false, true} (Boolean De Morgan algebra)
-- At weight true (= 𝟙), we get standard MLTT
-- At weight false (= 𝟘), judgments are vacuously satisfied

open BoolDM

-- Import ProbTT typing with Boolean weights
open Typing BoolDM

-- Standard MLTT typing (no weights)
-- This is the target of the embedding
data _⊢mltt_∶_ : ∀ {n} → Ctx n → Tm n → Ty n → Set where
  -- Variable
  mltt-var : ∀ {n} {Γ : Ctx n} (i : Fin n) →
             Γ ⊢mltt var i ∶ lookup Γ i

  -- Π-Intro
  mltt-lam : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {b : Tm (suc n)} →
             (Γ , A) ⊢mltt b ∶ B →
             Γ ⊢mltt lam A b ∶ (A ⇒ B)

  -- Π-Elim
  mltt-app : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {f a : Tm n} →
             Γ ⊢mltt f ∶ (A ⇒ B) →
             Γ ⊢mltt a ∶ A →
             Γ ⊢mltt app f a ∶ (B [ a ]ₜ)

  -- Σ-Intro
  mltt-pair : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} →
              Γ ⊢mltt a ∶ A →
              Γ ⊢mltt b ∶ (B [ a ]ₜ) →
              Γ ⊢mltt pair a b ∶ (A ×' B)

  -- Σ-Elim
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
  mltt-case : ∀ {n} {Γ : Ctx n} {A B C : Ty n} {e : Tm n} {l r : Tm (suc n)} →
              Γ ⊢mltt e ∶ (A +' B) →
              (Γ , A) ⊢mltt l ∶ wkTy C →
              (Γ , B) ⊢mltt r ∶ wkTy C →
              Γ ⊢mltt case e l r ∶ C

  -- 𝟙-Intro
  mltt-star : ∀ {n} {Γ : Ctx n} →
              Γ ⊢mltt star ∶ 𝟙'

  -- 𝟘-Elim
  mltt-abort : ∀ {n} {Γ : Ctx n} {A : Ty n} {e : Tm n} →
               Γ ⊢mltt e ∶ 𝟘' →
               Γ ⊢mltt abort A e ∶ A

  -- Id-Intro
  mltt-refl : ∀ {n} {Γ : Ctx n} {A : Ty n} {a : Tm n} →
              Γ ⊢mltt a ∶ A →
              Γ ⊢mltt refl' ∶ Id A a a

  -- Id-Elim
  mltt-J : ∀ {n} {Γ : Ctx n} {A : Ty n} {a b : Tm n}
             {M : Ty (suc (suc n))} {d p : Tm n} →
           Γ ⊢mltt p ∶ Id A a b →
           Γ ⊢mltt d ∶ (M [ a ]ₜ [ refl' ]ₜ) →
           Γ ⊢mltt J M d p ∶ (M [ b ]ₜ [ p ]ₜ)

-- Key fact: true · true = true in Boolean algebra
-- This means weights compose trivially at weight 1
∧-true-true : true ∧B true ≡ true
∧-true-true = refl

-- Embedding: MLTT → ProbTT @ true
-- An MLTT judgment becomes a ProbTT judgment at weight 𝟙
embed : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} →
        Γ ⊢mltt t ∶ A →
        Γ ⊢ t ∶ A @ true
embed (mltt-var i) = t-var i
embed (mltt-lam d) = t-lam (embed d)
embed (mltt-app df da) = subst-weight (t-app (embed df) (embed da)) ∧-true-true
  where
    subst-weight : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w w' : Bool} →
                   Γ ⊢ t ∶ A @ w →
                   w ≡ w' →
                   Γ ⊢ t ∶ A @ w'
    subst-weight d refl = d
embed (mltt-pair da db) = subst-weight (t-pair (embed da) (embed db)) ∧-true-true
  where
    subst-weight : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w w' : Bool} →
                   Γ ⊢ t ∶ A @ w →
                   w ≡ w' →
                   Γ ⊢ t ∶ A @ w'
    subst-weight d refl = d
embed (mltt-fst d) = t-fst (embed d)
embed (mltt-snd d) = t-snd (embed d)
embed (mltt-inl d) = t-inl (embed d)
embed (mltt-inr d) = t-inr (embed d)
embed (mltt-case de dl dr) = subst-weight (t-case (embed de) (embed dl) (embed dr)) ∧-true-true
  where
    subst-weight : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w w' : Bool} →
                   Γ ⊢ t ∶ A @ w →
                   w ≡ w' →
                   Γ ⊢ t ∶ A @ w'
    subst-weight d refl = d
embed mltt-star = t-star
embed (mltt-abort d) = t-abort (embed d)
embed (mltt-refl d) = t-refl (embed d)
embed (mltt-J dp dd) = subst-weight (t-J (embed dp) (embed dd)) ∧-true-true
  where
    subst-weight : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w w' : Bool} →
                   Γ ⊢ t ∶ A @ w →
                   w ≡ w' →
                   Γ ⊢ t ∶ A @ w'
    subst-weight d refl = d

-- Collapse: ProbTT @ true → MLTT
-- A ProbTT judgment at weight 𝟙 gives an MLTT judgment
-- This requires the derivation to be at exactly weight true (not just ≤ true)
collapse : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} →
           Γ ⊢ t ∶ A @ true →
           Γ ⊢mltt t ∶ A
collapse (t-var i) = mltt-var i
collapse (t-weaken d ≤-true) = collapse d
collapse (t-lam d) = mltt-lam (collapse d)
collapse (t-app {w = true} {v = true} df da) = mltt-app (collapse df) (collapse da)
collapse (t-pair {w = true} {v = true} da db) = mltt-pair (collapse da) (collapse db)
collapse (t-fst d) = mltt-fst (collapse d)
collapse (t-snd d) = mltt-snd (collapse d)
collapse (t-inl d) = mltt-inl (collapse d)
collapse (t-inr d) = mltt-inr (collapse d)
collapse (t-case {w = true} {v = true} de dl dr) = mltt-case (collapse de) (collapse dl) (collapse dr)
collapse t-star = mltt-star
collapse (t-abort d) = mltt-abort (collapse d)
collapse (t-refl d) = mltt-refl (collapse d)
collapse (t-J {w = true} {v = true} dp dd) = mltt-J (collapse dp) (collapse dd)

-- Round-trip: embed then collapse is identity
embed-collapse : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n}
                   (d : Γ ⊢mltt t ∶ A) →
                 collapse (embed d) ≡ d
embed-collapse (mltt-var i) = refl
embed-collapse (mltt-lam d) = cong mltt-lam (embed-collapse d)
embed-collapse (mltt-app df da) = cong₂ mltt-app (embed-collapse df) (embed-collapse da)
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
    cong₂ f refl refl = refl
embed-collapse (mltt-pair da db) = cong₂ mltt-pair (embed-collapse da) (embed-collapse db)
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
    cong₂ f refl refl = refl
embed-collapse (mltt-fst d) = cong mltt-fst (embed-collapse d)
embed-collapse (mltt-snd d) = cong mltt-snd (embed-collapse d)
embed-collapse (mltt-inl d) = cong mltt-inl (embed-collapse d)
embed-collapse (mltt-inr d) = cong mltt-inr (embed-collapse d)
embed-collapse (mltt-case de dl dr) = cong₃ mltt-case (embed-collapse de) (embed-collapse dl) (embed-collapse dr)
  where
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
    cong₃ f refl refl refl = refl
embed-collapse mltt-star = refl
embed-collapse (mltt-abort d) = cong mltt-abort (embed-collapse d)
embed-collapse (mltt-refl d) = cong mltt-refl (embed-collapse d)
embed-collapse (mltt-J dp dd) = cong₂ mltt-J (embed-collapse dp) (embed-collapse dd)
  where
    cong₂ : ∀ {A B C : Set} (f : A → B → C) {x₁ x₂ : A} {y₁ y₂ : B} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
    cong₂ f refl refl = refl
