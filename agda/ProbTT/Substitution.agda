module ProbTT.Substitution where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import ProbTT.Syntax

-- Renamings: Fin m → Fin n
Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

-- Substitutions: Fin m → Tm n
Sub : ℕ → ℕ → Set
Sub m n = Fin m → Tm n

-- Lift a renaming under a binder
liftRen : ∀ {m n} → Ren m n → Ren (suc m) (suc n)
liftRen ρ zero    = zero
liftRen ρ (suc i) = suc (ρ i)

-- Weaken renaming (shift all indices)
wkRen : ∀ {m n} → Ren m n → Ren m (suc n)
wkRen ρ i = suc (ρ i)

-- Identity renaming
idRen : ∀ {n} → Ren n n
idRen i = i

-- Apply renaming to terms (mutually recursive with renTy)
mutual
  renTm : ∀ {m n} → Ren m n → Tm m → Tm n
  renTm ρ (var i)       = var (ρ i)
  renTm ρ (lam A t)     = lam (renTy ρ A) (renTm (liftRen ρ) t)
  renTm ρ (app f a)     = app (renTm ρ f) (renTm ρ a)
  renTm ρ (pair a b)    = pair (renTm ρ a) (renTm ρ b)
  renTm ρ (fst t)       = fst (renTm ρ t)
  renTm ρ (snd t)       = snd (renTm ρ t)
  renTm ρ (inl a)       = inl (renTm ρ a)
  renTm ρ (inr b)       = inr (renTm ρ b)
  renTm ρ (case e l r)  = case (renTm ρ e) (renTm (liftRen ρ) l) (renTm (liftRen ρ) r)
  renTm ρ refl'         = refl'
  renTm ρ (J M d p)     = J (renTy (liftRen (liftRen ρ)) M) (renTm ρ d) (renTm ρ p)

  renTy : ∀ {m n} → Ren m n → Ty m → Ty n
  renTy ρ (base i)   = base i
  renTy ρ (A ⇒ B)    = renTy ρ A ⇒ renTy (liftRen ρ) B
  renTy ρ (A ×' B)   = renTy ρ A ×' renTy (liftRen ρ) B
  renTy ρ (A +' B)   = renTy ρ A +' renTy ρ B
  renTy ρ (Id A a b) = Id (renTy ρ A) (renTm ρ a) (renTm ρ b)

-- Weakening: wkTm and wkTy are defined in Syntax.agda and re-exported here.
-- They are equivalent to renTm suc and renTy suc respectively.

-- Lift a substitution under a binder
liftSub : ∀ {m n} → Sub m n → Sub (suc m) (suc n)
liftSub σ zero    = var zero
liftSub σ (suc i) = wkTm (σ i)

-- Identity substitution
idSub : ∀ {n} → Sub n n
idSub = var

-- Single-variable substitution: replace var 0 with t, shift others down
singleSub : ∀ {n} → Tm n → Sub (suc n) n
singleSub t zero    = t
singleSub t (suc i) = var i

-- Apply substitution to terms (mutually recursive with substTy)
mutual
  substTm : ∀ {m n} → Sub m n → Tm m → Tm n
  substTm σ (var i)       = σ i
  substTm σ (lam A t)     = lam (substTy σ A) (substTm (liftSub σ) t)
  substTm σ (app f a)     = app (substTm σ f) (substTm σ a)
  substTm σ (pair a b)    = pair (substTm σ a) (substTm σ b)
  substTm σ (fst t)       = fst (substTm σ t)
  substTm σ (snd t)       = snd (substTm σ t)
  substTm σ (inl a)       = inl (substTm σ a)
  substTm σ (inr b)       = inr (substTm σ b)
  substTm σ (case e l r)  = case (substTm σ e) (substTm (liftSub σ) l) (substTm (liftSub σ) r)
  substTm σ refl'         = refl'
  substTm σ (J M d p)     = J (substTy (liftSub (liftSub σ)) M) (substTm σ d) (substTm σ p)

  substTy : ∀ {m n} → Sub m n → Ty m → Ty n
  substTy σ (base i)   = base i
  substTy σ (A ⇒ B)    = substTy σ A ⇒ substTy (liftSub σ) B
  substTy σ (A ×' B)   = substTy σ A ×' substTy (liftSub σ) B
  substTy σ (A +' B)   = substTy σ A +' substTy σ B
  substTy σ (Id A a b) = Id (substTy σ A) (substTm σ a) (substTm σ b)

-- Convenient notation for single substitution
_[_] : ∀ {n} → Tm (suc n) → Tm n → Tm n
t [ a ] = substTm (singleSub a) t

_[_]ₜ : ∀ {n} → Ty (suc n) → Tm n → Ty n
A [ a ]ₜ = substTy (singleSub a) A

-- Double substitution: replace both var 0 and var 1
-- In context Γ,x,p: var 0 = p, var 1 = x
-- doubleSub p-val x-val gives: 0 ↦ p-val, 1 ↦ x-val
doubleSub : ∀ {n} → Tm n → Tm n → Sub (suc (suc n)) n
doubleSub t₀ t₁ zero          = t₀
doubleSub t₀ t₁ (suc zero)    = t₁
doubleSub t₀ t₁ (suc (suc i)) = var i

-- Double substitution for types: A [ t₀ , t₁ ]₂ₜ
-- Substitutes t₀ for var 0 and t₁ for var 1
_[_,_]₂ₜ : ∀ {n} → Ty (suc (suc n)) → Tm n → Tm n → Ty n
A [ t₀ , t₁ ]₂ₜ = substTy (doubleSub t₀ t₁) A

-- Key lemma: substituting var gives the term
subst-var : ∀ {n} (t : Tm n) → var zero [ t ] ≡ t
subst-var t = refl

-- Helper: cong₃ for 3-argument functions
cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
        x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

-- Identity substitution is identity (simplified version without full proof)
-- The full proof requires showing liftSub idSub = idSub extensionally
-- For now we postulate these standard lemmas

postulate
  subst-id-tm : ∀ {n} (t : Tm n) → substTm idSub t ≡ t
  subst-id-ty : ∀ {n} (A : Ty n) → substTy idSub A ≡ A
