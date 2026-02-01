module ProbTT.Examples where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Substitution
open import ProbTT.Context
open import ProbTT.Judgment

-- Examples using Boolean weights (the MLTT case)
module BoolExamples where
  open BoolDM
  open Typing BoolDM

  -- A base type for examples
  Nat : ∀ {n} → Ty n
  Nat = base 0

  -- Identity function: λx.x : A → A @ 𝟙
  -- The identity always has weight 1
  id-term : ∀ {n} → Tm n
  id-term = lam Nat (var zero)

  id-typed : ∀ {n} {Γ : Ctx n} → Γ ⊢ id-term ∶ (Nat ⇒ wkTy Nat) @ true
  id-typed = t-lam (t-var zero)

  -- Application of identity: id a : A @ w when a : A @ w
  -- Weight is preserved through identity
  id-app : ∀ {n} {Γ : Ctx n} {a : Tm n} {w : Bool} →
           Γ ⊢ a ∶ Nat @ w →
           Γ ⊢ app id-term a ∶ Nat @ w
  id-app {w = w} d = subst-eq (t-app id-typed d) (∧-identityˡ w)
    where
      subst-eq : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w w' : Bool} →
                 Γ ⊢ t ∶ A @ w →
                 w ≡ w' →
                 Γ ⊢ t ∶ A @ w'
      subst-eq d refl = d

  -- Pair: (a, b) : A × B @ w·v
  -- The joint weight is the product
  pair-example : ∀ {n} {Γ : Ctx n} {a b : Tm n} {w v : Bool} →
                 Γ ⊢ a ∶ Nat @ w →
                 Γ ⊢ b ∶ Nat @ v →
                 Γ ⊢ pair a b ∶ (Nat ×' wkTy Nat) @ (w ∧B v)
  pair-example da db = t-pair da db

  -- Weight multiplication: at weight true, composition works normally
  -- f : A → B @ 𝟙, g : B → C @ 𝟙 ⊢ g ∘ f : A → C @ 𝟙
  compose-term : ∀ {n} → Tm (suc (suc n))
  compose-term = lam Nat (app (var (suc zero)) (app (var (suc (suc zero))) (var zero)))

  -- Ex falso: from ⊥ at any weight, we get anything at that weight
  ex-falso-example : ∀ {n} {Γ : Ctx n} {e : Tm n} {w : Bool} →
                     Γ ⊢ e ∶ 𝟘' @ w →
                     Γ ⊢ abort Nat e ∶ Nat @ w
  ex-falso-example = t-abort

  -- At weight false (= 𝟘), everything is trivially inhabited
  -- This is because false · v = false for any v
  weight-zero-trivial : ∀ (v : Bool) → false ∧B v ≡ false
  weight-zero-trivial v = refl

  -- Unit introduction: ⋆ : 𝟙 @ 𝟙
  unit-intro : ∀ {n} {Γ : Ctx n} → Γ ⊢ star ∶ 𝟙' @ true
  unit-intro = t-star

  -- Sum case: demonstrate weight multiplication in elimination
  -- case e of inl x → l | inr y → r : C @ w·v
  sum-elim-example : ∀ {n} {Γ : Ctx n} {e : Tm n} {w v : Bool} →
                     Γ ⊢ e ∶ (Nat +' Nat) @ w →
                     (Γ , Nat) ⊢ var zero ∶ wkTy Nat @ v →
                     (Γ , Nat) ⊢ var zero ∶ wkTy Nat @ v →
                     Γ ⊢ case e (var zero) (var zero) ∶ Nat @ (w ∧B v)
  sum-elim-example = t-case

-- Key insight: In Boolean algebra, true · true = true
-- This means at weight 1, composition preserves full certainty.
-- But at any lower weight, multiplication reduces certainty.

-- Example: If P(A) = 0.9 and P(B|A) = 0.9, then P(A,B) = 0.81
-- In Boolean: true · true = true (full certainty preserved)
-- In [0,1]: 0.9 · 0.9 = 0.81 (certainty reduces)
