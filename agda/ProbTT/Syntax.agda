module ProbTT.Syntax where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Well-scoped types and terms (mutually recursive)
-- n = number of type/term variables in scope
-- Pure ProbTT: No Empty type (𝟘') and no Unit type (𝟙').
-- Impossibility is weight 0, not a special type.
-- Certainty is weight 1, not a special type.
-- This avoids MLTT-style explosion and keeps the system philosophically pure.

mutual
  data Ty (n : ℕ) : Set where
    base : ℕ → Ty n                        -- base types (indexed family)
    _⇒_  : Ty n → Ty (suc n) → Ty n        -- Π (dependent function)
    _×'_ : Ty n → Ty (suc n) → Ty n        -- Σ (dependent pair)
    _+'_ : Ty n → Ty n → Ty n              -- coproduct (sum)
    Id   : Ty n → Tm n → Tm n → Ty n       -- identity type

  -- Well-scoped terms
  -- n = number of term variables in scope
  data Tm (n : ℕ) : Set where
    -- Variables (de Bruijn indices, scope-safe)
    var   : Fin n → Tm n

    -- Function
    lam   : Ty n → Tm (suc n) → Tm n       -- λ(x:A).b
    app   : Tm n → Tm n → Tm n             -- f a

    -- Pair (dependent)
    pair  : Tm n → Tm n → Tm n             -- (a, b)
    fst   : Tm n → Tm n                    -- π₁ t
    snd   : Tm n → Tm n                    -- π₂ t

    -- Sum
    inl   : Tm n → Tm n                    -- inl a
    inr   : Tm n → Tm n                    -- inr b
    case  : Tm n → Tm (suc n) → Tm (suc n) → Tm n  -- case e of inl x → l | inr y → r

    -- Identity
    refl' : Tm n                           -- refl

    -- Identity elimination (J)
    J     : Ty (suc (suc n))               -- motive: (x:A)(p:Id A a x) → Type
        → Tm n                             -- base case: M[a, refl]
        → Tm n                             -- proof term: p : Id A a b
        → Tm n                             -- result

infixr 5 _⇒_
infixr 6 _×'_
infixr 6 _+'_

-- Simple (non-dependent) function type
_→'_ : ∀ {n} → Ty n → Ty n → Ty n
A →' B = A ⇒ wkTy B
  where
    -- Weakening for types (adds unused variable)
    mutual
      wkTy : ∀ {n} → Ty n → Ty (suc n)
      wkTy (base i)   = base i
      wkTy (A ⇒ B)    = wkTy A ⇒ wkTy B
      wkTy (A ×' B)   = wkTy A ×' wkTy B
      wkTy (A +' B)   = wkTy A +' wkTy B
      wkTy (Id A a b) = Id (wkTy A) (wkTm a) (wkTm b)

      wkTm : ∀ {n} → Tm n → Tm (suc n)
      wkTm (var i)       = var (suc i)
      wkTm (lam A t)     = lam (wkTy A) (wkTm t)
      wkTm (app f a)     = app (wkTm f) (wkTm a)
      wkTm (pair a b)    = pair (wkTm a) (wkTm b)
      wkTm (fst t)       = fst (wkTm t)
      wkTm (snd t)       = snd (wkTm t)
      wkTm (inl a)       = inl (wkTm a)
      wkTm (inr b)       = inr (wkTm b)
      wkTm (case e l r)  = case (wkTm e) (wkTm l) (wkTm r)
      wkTm refl'         = refl'
      wkTm (J M d p)     = J (wkTy M) (wkTm d) (wkTm p)

-- Simple (non-dependent) product type
_×''_ : ∀ {n} → Ty n → Ty n → Ty n
A ×'' B = A ×' wkTy B
  where
    mutual
      wkTy : ∀ {n} → Ty n → Ty (suc n)
      wkTy (base i)   = base i
      wkTy (A ⇒ B)    = wkTy A ⇒ wkTy B
      wkTy (A ×' B)   = wkTy A ×' wkTy B
      wkTy (A +' B)   = wkTy A +' wkTy B
      wkTy (Id A a b) = Id (wkTy A) (wkTm a) (wkTm b)

      wkTm : ∀ {n} → Tm n → Tm (suc n)
      wkTm (var i)       = var (suc i)
      wkTm (lam A t)     = lam (wkTy A) (wkTm t)
      wkTm (app f a)     = app (wkTm f) (wkTm a)
      wkTm (pair a b)    = pair (wkTm a) (wkTm b)
      wkTm (fst t)       = fst (wkTm t)
      wkTm (snd t)       = snd (wkTm t)
      wkTm (inl a)       = inl (wkTm a)
      wkTm (inr b)       = inr (wkTm b)
      wkTm (case e l r)  = case (wkTm e) (wkTm l) (wkTm r)
      wkTm refl'         = refl'
      wkTm (J M d p)     = J (wkTy M) (wkTm d) (wkTm p)
