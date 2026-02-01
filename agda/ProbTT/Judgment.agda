module ProbTT.Judgment where

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Substitution
open import ProbTT.Context

-- Parameterized by a De Morgan algebra
module Typing {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- Type formation judgment: Γ ⊢ A type
  data _⊢_type : ∀ {n} → Ctx n → Ty n → Set ℓ where
    -- Base types are always well-formed
    base-form : ∀ {n} {Γ : Ctx n} (i : ℕ) →
                Γ ⊢ base i type

    -- Π-types: (x:A) → B requires A type in Γ and B type in Γ,x:A
    Π-form : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} →
             Γ ⊢ A type →
             (Γ , A) ⊢ B type →
             Γ ⊢ (A ⇒ B) type

    -- Σ-types: Σ(x:A).B
    Σ-form : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} →
             Γ ⊢ A type →
             (Γ , A) ⊢ B type →
             Γ ⊢ (A ×' B) type

    -- Sum types: A + B
    +-form : ∀ {n} {Γ : Ctx n} {A B : Ty n} →
             Γ ⊢ A type →
             Γ ⊢ B type →
             Γ ⊢ (A +' B) type

    -- Unit type
    𝟙-form : ∀ {n} {Γ : Ctx n} →
             Γ ⊢ 𝟙' type

    -- Empty type
    𝟘-form : ∀ {n} {Γ : Ctx n} →
             Γ ⊢ 𝟘' type

    -- Identity type: requires endpoints at weight 𝟙
    Id-form : ∀ {n} {Γ : Ctx n} {A : Ty n} {a b : Tm n} →
              Γ ⊢ A type →
              Γ ⊢ a ∶ A @ 𝟙 →
              Γ ⊢ b ∶ A @ 𝟙 →
              Γ ⊢ Id A a b type

  -- Weighted typing judgment: Γ ⊢ t : A @ w
  -- The key insight: weights multiply in elimination
  data _⊢_∶_@_ : ∀ {n} → Ctx n → Tm n → Ty n → W → Set ℓ where

    -- Variable: always weight 𝟙
    t-var : ∀ {n} {Γ : Ctx n} (i : Fin n) →
            Γ ⊢ var i ∶ lookup Γ i @ 𝟙

    -- Weight weakening: can lower weight
    t-weaken : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w v : W} →
               Γ ⊢ t ∶ A @ w →
               v ≤ w →
               Γ ⊢ t ∶ A @ v

    -- Π-Intro: λ(x:A).b : (x:A) → B @ w
    t-lam : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {b : Tm (suc n)} {w : W} →
            (Γ , A) ⊢ b ∶ B @ w →
            Γ ⊢ lam A b ∶ (A ⇒ B) @ w

    -- Π-Elim: WEIGHTS MULTIPLY
    -- f : (x:A) → B @ w, a : A @ v ⊢ f a : B[a] @ w·v
    t-app : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {f a : Tm n} {w v : W} →
            Γ ⊢ f ∶ (A ⇒ B) @ w →
            Γ ⊢ a ∶ A @ v →
            Γ ⊢ app f a ∶ (B [ a ]ₜ) @ (w · v)

    -- Σ-Intro: (a,b) : Σ(x:A).B @ w·v
    -- Pair weight = product of component weights (joint probability)
    t-pair : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {w v : W} →
             Γ ⊢ a ∶ A @ w →
             Γ ⊢ b ∶ (B [ a ]ₜ) @ v →
             Γ ⊢ pair a b ∶ (A ×' B) @ (w · v)

    -- Σ-Elim₁: π₁ t : A @ w
    t-fst : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {t : Tm n} {w : W} →
            Γ ⊢ t ∶ (A ×' B) @ w →
            Γ ⊢ fst t ∶ A @ w

    -- Σ-Elim₂: π₂ t : B[π₁ t] @ w
    t-snd : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {t : Tm n} {w : W} →
            Γ ⊢ t ∶ (A ×' B) @ w →
            Γ ⊢ snd t ∶ (B [ fst t ]ₜ) @ w

    -- +-Intro: inl a : A + B @ w
    t-inl : ∀ {n} {Γ : Ctx n} {A B : Ty n} {a : Tm n} {w : W} →
            Γ ⊢ a ∶ A @ w →
            Γ ⊢ inl a ∶ (A +' B) @ w

    -- +-Intro: inr b : A + B @ w
    t-inr : ∀ {n} {Γ : Ctx n} {A B : Ty n} {b : Tm n} {w : W} →
            Γ ⊢ b ∶ B @ w →
            Γ ⊢ inr b ∶ (A +' B) @ w

    -- +-Elim: WEIGHTS MULTIPLY (critical rule that was missing!)
    -- case e of inl x → l | inr y → r : C @ w·v
    t-case : ∀ {n} {Γ : Ctx n} {A B C : Ty n} {e : Tm n} {l r : Tm (suc n)} {w v : W} →
             Γ ⊢ e ∶ (A +' B) @ w →
             (Γ , A) ⊢ l ∶ wkTy C @ v →
             (Γ , B) ⊢ r ∶ wkTy C @ v →
             Γ ⊢ case e l r ∶ C @ (w · v)

    -- 𝟙-Intro: ⋆ : 𝟙 @ 𝟙
    t-star : ∀ {n} {Γ : Ctx n} →
             Γ ⊢ star ∶ 𝟙' @ 𝟙

    -- 𝟘-Elim: abort e : A @ w (ex falso)
    -- From falsehood, anything follows with the same weight
    t-abort : ∀ {n} {Γ : Ctx n} {A : Ty n} {e : Tm n} {w : W} →
              Γ ⊢ e ∶ 𝟘' @ w →
              Γ ⊢ abort A e ∶ A @ w

    -- Id-Intro: refl : Id A a a @ w
    t-refl : ∀ {n} {Γ : Ctx n} {A : Ty n} {a : Tm n} {w : W} →
             Γ ⊢ a ∶ A @ w →
             Γ ⊢ refl' ∶ Id A a a @ w

    -- Id-Elim (J): transport along equality
    -- If p : Id A a b @ w and d : M[a,refl] @ v
    -- then J M d p : M[b,p] @ w·v
    t-J : ∀ {n} {Γ : Ctx n} {A : Ty n} {a b : Tm n}
            {M : Ty (suc (suc n))} {d p : Tm n} {w v : W} →
          Γ ⊢ p ∶ Id A a b @ w →
          Γ ⊢ d ∶ (M [ a ]ₜ [ refl' ]ₜ) @ v →
          Γ ⊢ J M d p ∶ (M [ b ]ₜ [ p ]ₜ) @ (w · v)

  -- Definitional equality (computation/beta rules)
  data _⊢_≡_∶_@_ : ∀ {n} → Ctx n → Tm n → Tm n → Ty n → W → Set ℓ where

    -- Reflexivity
    eq-refl : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w : W} →
              Γ ⊢ t ∶ A @ w →
              Γ ⊢ t ≡ t ∶ A @ w

    -- Symmetry
    eq-sym : ∀ {n} {Γ : Ctx n} {s t : Tm n} {A : Ty n} {w : W} →
             Γ ⊢ s ≡ t ∶ A @ w →
             Γ ⊢ t ≡ s ∶ A @ w

    -- Transitivity
    eq-trans : ∀ {n} {Γ : Ctx n} {s t u : Tm n} {A : Ty n} {w : W} →
               Γ ⊢ s ≡ t ∶ A @ w →
               Γ ⊢ t ≡ u ∶ A @ w →
               Γ ⊢ s ≡ u ∶ A @ w

    -- Π-β: (λx.b) a ≡ b[a]
    Π-β : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {b : Tm (suc n)} {a : Tm n} {w v : W} →
          (Γ , A) ⊢ b ∶ B @ w →
          Γ ⊢ a ∶ A @ v →
          Γ ⊢ app (lam A b) a ≡ (b [ a ]) ∶ (B [ a ]ₜ) @ (w · v)

    -- Σ-β₁: π₁(a,b) ≡ a
    Σ-β₁ : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {w v : W} →
           Γ ⊢ a ∶ A @ w →
           Γ ⊢ b ∶ (B [ a ]ₜ) @ v →
           Γ ⊢ fst (pair a b) ≡ a ∶ A @ (w · v)

    -- Σ-β₂: π₂(a,b) ≡ b
    Σ-β₂ : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {w v : W} →
           Γ ⊢ a ∶ A @ w →
           Γ ⊢ b ∶ (B [ a ]ₜ) @ v →
           Γ ⊢ snd (pair a b) ≡ b ∶ (B [ a ]ₜ) @ (w · v)

    -- +-β-inl: case (inl a) l r ≡ l[a]
    +-β-inl : ∀ {n} {Γ : Ctx n} {A B C : Ty n} {a : Tm n} {l r : Tm (suc n)} {w v : W} →
              Γ ⊢ a ∶ A @ w →
              (Γ , A) ⊢ l ∶ wkTy C @ v →
              (Γ , B) ⊢ r ∶ wkTy C @ v →
              Γ ⊢ case (inl a) l r ≡ (l [ a ]) ∶ C @ (w · v)

    -- +-β-inr: case (inr b) l r ≡ r[b]
    +-β-inr : ∀ {n} {Γ : Ctx n} {A B C : Ty n} {b : Tm n} {l r : Tm (suc n)} {w v : W} →
              Γ ⊢ b ∶ B @ w →
              (Γ , A) ⊢ l ∶ wkTy C @ v →
              (Γ , B) ⊢ r ∶ wkTy C @ v →
              Γ ⊢ case (inr b) l r ≡ (r [ b ]) ∶ C @ (w · v)

    -- Id-β: J M d refl ≡ d
    Id-β : ∀ {n} {Γ : Ctx n} {A : Ty n} {a : Tm n}
             {M : Ty (suc (suc n))} {d : Tm n} {w v : W} →
           Γ ⊢ a ∶ A @ w →
           Γ ⊢ d ∶ (M [ a ]ₜ [ refl' ]ₜ) @ v →
           Γ ⊢ J M d refl' ≡ d ∶ (M [ a ]ₜ [ refl' ]ₜ) @ (w · v)
