module ProbTT.Context where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)

open import ProbTT.Syntax
open import ProbTT.Substitution

-- Well-scoped contexts
-- Ctx n contains n types, each well-scoped for its position
data Ctx : ℕ → Set where
  ∅   : Ctx zero
  _,_ : ∀ {n} → Ctx n → Ty n → Ctx (suc n)

infixl 5 _,_

-- Lookup: get the type at position i in context Γ
-- The returned type is weakened appropriately
lookup : ∀ {n} → Ctx n → Fin n → Ty n
lookup (Γ , A) zero    = wkTy A
lookup (Γ , A) (suc i) = wkTy (lookup Γ i)

-- Context length (for convenience, though it equals n)
length : ∀ {n} → Ctx n → ℕ
length {n} _ = n
