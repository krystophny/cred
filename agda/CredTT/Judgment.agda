module CredTT.Judgment where

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CredTT.Credence
open import CredTT.Syntax
open import CredTT.Substitution
open import CredTT.Context

-- Parameterized by a De Morgan algebra
module Typing {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- PURE CredTT: No Empty type (Zero') and no Unit type (One').
  -- - Impossibility is credence 0 on any type, not a special type.
  -- - Certainty is credence 1 on any type, not a special type.
  -- This avoids the philosophical question "what TYPE is credence 0/1?"
  -- and keeps the system clean.

  -- Both judgments must be defined mutually because Id-form uses typing judgment
  -- Fixity declarations for judgment forms
  infix 3 _⊢_type
  infix 3 _⊢_∶_〔_〕
  infix 3 _⊢_≐_∶_〔_〕

  mutual
    -- Type formation judgment: Gamma |- A type
    data _⊢_type : ∀ {n} → Ctx n → Ty n → Set ℓ where
      -- Base types are always well-formed
      base-form : ∀ {n} {Γ : Ctx n} (i : ℕ) →
                  Γ ⊢ base i type

      -- Pi-types: (x:A) -> B requires A type in Gamma and B type in Gamma,x:A
      Π-form : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} →
               Γ ⊢ A type →
               (Γ , A) ⊢ B type →
               Γ ⊢ (A ⇒ B) type

      -- Sigma-types: Sigma(x:A).B
      Σ-form : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} →
               Γ ⊢ A type →
               (Γ , A) ⊢ B type →
               Γ ⊢ (A ×' B) type

      -- Sum types: A + B
      +-form : ∀ {n} {Γ : Ctx n} {A B : Ty n} →
               Γ ⊢ A type →
               Γ ⊢ B type →
               Γ ⊢ (A +' B) type

      -- Note: No Unit type (One') formation rule.
      -- Certainty is credence 1 on any type, not a special type.

      -- Note: No Empty type (Zero') formation rule.
      -- Impossibility is credence 0, not a special type.

      -- Identity type: requires endpoints at credence 1
      Id-form : ∀ {n} {Γ : Ctx n} {A : Ty n} {a b : Tm n} →
                Γ ⊢ A type →
                Γ ⊢ a ∶ A 〔 𝟙 〕 →
                Γ ⊢ b ∶ A 〔 𝟙 〕 →
                Γ ⊢ Id A a b type

    -- Credence-weighted typing judgment: Gamma |- t : A [ c ]
    -- The key insight: credences multiply in elimination
    --
    -- PROOF BY CONTRADICTION (Meta-Theorem):
    -- In CredTT, there is no Empty type (Zero') and no explosion rule (abort).
    -- Proof by contradiction works at the META level (in Agda), not the object level.
    --
    -- Meta-level: We can prove "if Gamma |- t : A [ 0 ], then <anything>" in Agda
    -- because credence 0 terms have no computational content we need to handle.
    --
    -- Object-level: CredTT terms cannot derive arbitrary conclusions from credence 0.
    -- Instead, conditioning on credence 0 is unconstrained (graded ex falso).
    data _⊢_∶_〔_〕 : ∀ {n} → Ctx n → Tm n → Ty n → C → Set ℓ where

      -- Variable: always credence 1
      t-var : ∀ {n} {Γ : Ctx n} (i : Fin n) →
              Γ ⊢ var i ∶ lookup Γ i 〔 𝟙 〕

      -- Credence weakening: can lower credence
      t-weaken : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c d : C} →
                 Γ ⊢ t ∶ A 〔 c 〕 →
                 d ≤ c →
                 Γ ⊢ t ∶ A 〔 d 〕

      -- Pi-Intro: lam(x:A).b : (x:A) -> B [ c ]
      t-lam : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {b : Tm (suc n)} {c : C} →
              (Γ , A) ⊢ b ∶ B 〔 c 〕 →
              Γ ⊢ lam A b ∶ (A ⇒ B) 〔 c 〕

      -- Pi-Elim: CREDENCES MULTIPLY
      -- f : (x:A) -> B [ c ], a : A [ d ] |- f a : B[a] [ c . d ]
      t-app : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {f a : Tm n} {c d : C} →
              Γ ⊢ f ∶ (A ⇒ B) 〔 c 〕 →
              Γ ⊢ a ∶ A 〔 d 〕 →
              Γ ⊢ app f a ∶ (B [ a ]ₜ) 〔 c · d 〕

      -- Sigma-Intro: (a,b) : Sigma(x:A).B [ c . d ]
      -- Pair credence = product of component credences (joint probability)
      t-pair : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {c d : C} →
               Γ ⊢ a ∶ A 〔 c 〕 →
               Γ ⊢ b ∶ (B [ a ]ₜ) 〔 d 〕 →
               Γ ⊢ pair a b ∶ (A ×' B) 〔 c · d 〕

      -- Sigma-Elim1: pi1 t : A [ c ]
      t-fst : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {t : Tm n} {c : C} →
              Γ ⊢ t ∶ (A ×' B) 〔 c 〕 →
              Γ ⊢ fst t ∶ A 〔 c 〕

      -- Sigma-Elim2: pi2 t : B[pi1 t] [ c ]
      t-snd : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {t : Tm n} {c : C} →
              Γ ⊢ t ∶ (A ×' B) 〔 c 〕 →
              Γ ⊢ snd t ∶ (B [ fst t ]ₜ) 〔 c 〕

      -- +-Intro: inl a : A + B [ c ]
      t-inl : ∀ {n} {Γ : Ctx n} {A B : Ty n} {a : Tm n} {c : C} →
              Γ ⊢ a ∶ A 〔 c 〕 →
              Γ ⊢ inl a ∶ (A +' B) 〔 c 〕

      -- +-Intro: inr b : A + B [ c ]
      t-inr : ∀ {n} {Γ : Ctx n} {A B : Ty n} {b : Tm n} {c : C} →
              Γ ⊢ b ∶ B 〔 c 〕 →
              Γ ⊢ inr b ∶ (A +' B) 〔 c 〕

      -- +-Elim: CREDENCES MULTIPLY (critical rule!)
      -- case e of inl x -> l | inr y -> r : D [ c . d ]
      t-case : ∀ {n} {Γ : Ctx n} {A B D : Ty n} {e : Tm n} {l r : Tm (suc n)} {c d : C} →
               Γ ⊢ e ∶ (A +' B) 〔 c 〕 →
               (Γ , A) ⊢ l ∶ wkTy D 〔 d 〕 →
               (Γ , B) ⊢ r ∶ wkTy D 〔 d 〕 →
               Γ ⊢ case e l r ∶ D 〔 c · d 〕

      -- Note: No One-Intro (star : One [ 1 ]) rule.
      -- Certainty is credence 1 on any type, not a special Unit type.

      -- Note: No Zero-Elim (abort) rule. Impossibility is handled by credence 0.
      -- If a : A [ 0 ], then f a : B [ c . 0 ] = 0 automatically via credence multiplication.
      -- No explosion, no special rule needed.

      -- Id-Intro: refl : Id A a a [ c ]
      t-refl : ∀ {n} {Γ : Ctx n} {A : Ty n} {a : Tm n} {c : C} →
               Γ ⊢ a ∶ A 〔 c 〕 →
               Γ ⊢ refl' ∶ Id A a a 〔 c 〕

      -- Id-Elim (J): transport along equality
      -- If p : Id A a b [ c ] and d : M[a,refl] [ e ]
      -- then J M d p : M[b,p] [ c . e ]
      -- M has context Gamma,x:A,p:Id where var 0 = p, var 1 = x
      t-J : ∀ {n} {Γ : Ctx n} {A : Ty n} {a b : Tm n}
              {M : Ty (suc (suc n))} {d p : Tm n} {c e : C} →
            Γ ⊢ p ∶ Id A a b 〔 c 〕 →
            Γ ⊢ d ∶ (M [ refl' , a ]₂ₜ) 〔 e 〕 →
            Γ ⊢ J M d p ∶ (M [ p , b ]₂ₜ) 〔 c · e 〕

  -- Definitional equality (computation/beta rules)
  data _⊢_≐_∶_〔_〕 : ∀ {n} → Ctx n → Tm n → Tm n → Ty n → C → Set ℓ where

    -- Reflexivity
    eq-refl : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c : C} →
              Γ ⊢ t ∶ A 〔 c 〕 →
              Γ ⊢ t ≐ t ∶ A 〔 c 〕

    -- Symmetry
    eq-sym : ∀ {n} {Γ : Ctx n} {s t : Tm n} {A : Ty n} {c : C} →
             Γ ⊢ s ≐ t ∶ A 〔 c 〕 →
             Γ ⊢ t ≐ s ∶ A 〔 c 〕

    -- Transitivity
    eq-trans : ∀ {n} {Γ : Ctx n} {s t u : Tm n} {A : Ty n} {c : C} →
               Γ ⊢ s ≐ t ∶ A 〔 c 〕 →
               Γ ⊢ t ≐ u ∶ A 〔 c 〕 →
               Γ ⊢ s ≐ u ∶ A 〔 c 〕

    -- Pi-beta: (lam x.b) a = b[a]
    Π-β : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {b : Tm (suc n)} {a : Tm n} {c d : C} →
          (Γ , A) ⊢ b ∶ B 〔 c 〕 →
          Γ ⊢ a ∶ A 〔 d 〕 →
          Γ ⊢ app (lam A b) a ≐ (b [ a ]) ∶ (B [ a ]ₜ) 〔 c · d 〕

    -- Sigma-beta1: pi1(a,b) = a
    Σ-β₁ : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {c d : C} →
           Γ ⊢ a ∶ A 〔 c 〕 →
           Γ ⊢ b ∶ (B [ a ]ₜ) 〔 d 〕 →
           Γ ⊢ fst (pair a b) ≐ a ∶ A 〔 c · d 〕

    -- Sigma-beta2: pi2(a,b) = b
    Σ-β₂ : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {c d : C} →
           Γ ⊢ a ∶ A 〔 c 〕 →
           Γ ⊢ b ∶ (B [ a ]ₜ) 〔 d 〕 →
           Γ ⊢ snd (pair a b) ≐ b ∶ (B [ a ]ₜ) 〔 c · d 〕

    -- +-beta-inl: case (inl a) l r = l[a]
    +-β-inl : ∀ {n} {Γ : Ctx n} {A B D : Ty n} {a : Tm n} {l r : Tm (suc n)} {c d : C} →
              Γ ⊢ a ∶ A 〔 c 〕 →
              (Γ , A) ⊢ l ∶ wkTy D 〔 d 〕 →
              (Γ , B) ⊢ r ∶ wkTy D 〔 d 〕 →
              Γ ⊢ case (inl a) l r ≐ (l [ a ]) ∶ D 〔 c · d 〕

    -- +-beta-inr: case (inr b) l r = r[b]
    +-β-inr : ∀ {n} {Γ : Ctx n} {A B D : Ty n} {b : Tm n} {l r : Tm (suc n)} {c d : C} →
              Γ ⊢ b ∶ B 〔 c 〕 →
              (Γ , A) ⊢ l ∶ wkTy D 〔 d 〕 →
              (Γ , B) ⊢ r ∶ wkTy D 〔 d 〕 →
              Γ ⊢ case (inr b) l r ≐ (r [ b ]) ∶ D 〔 c · d 〕

    -- Id-beta: J M d refl = d
    Id-β : ∀ {n} {Γ : Ctx n} {A : Ty n} {a : Tm n}
             {M : Ty (suc (suc n))} {d : Tm n} {c e : C} →
           Γ ⊢ a ∶ A 〔 c 〕 →
           Γ ⊢ d ∶ (M [ refl' , a ]₂ₜ) 〔 e 〕 →
           Γ ⊢ J M d refl' ≐ d ∶ (M [ refl' , a ]₂ₜ) 〔 c · e 〕
