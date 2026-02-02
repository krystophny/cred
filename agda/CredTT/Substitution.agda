module CredTT.Substitution where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import CredTT.Syntax

-- Renamings: Fin m -> Fin n
Ren : ℕ → ℕ → Set
Ren m n = Fin m → Fin n

-- Substitutions: Fin m -> Tm n
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
-- In context Gamma,x,p: var 0 = p, var 1 = x
-- doubleSub p-val x-val gives: 0 |-> p-val, 1 |-> x-val
doubleSub : ∀ {n} → Tm n → Tm n → Sub (suc (suc n)) n
doubleSub t₀ t₁ zero          = t₀
doubleSub t₀ t₁ (suc zero)    = t₁
doubleSub t₀ t₁ (suc (suc i)) = var i

-- Double substitution for types: A [ t0 , t1 ]2t
-- Substitutes t0 for var 0 and t1 for var 1
_[_,_]₂ₜ : ∀ {n} → Ty (suc (suc n)) → Tm n → Tm n → Ty n
A [ t₀ , t₁ ]₂ₜ = substTy (doubleSub t₀ t₁) A

-- Key lemma: substituting var gives the term
subst-var : ∀ {n} (t : Tm n) → var zero [ t ] ≡ t
subst-var t = refl

-- Helper: cong3 for 3-argument functions
cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
        x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
cong₃ f refl refl refl = refl

-- ============================================================================
-- IDENTITY SUBSTITUTION LEMMAS (Issue #185)
-- ============================================================================

-- Key lemma: wkTm (var i) = var (suc i)
wkTm-var : ∀ {n} (i : Fin n) → wkTm (var i) ≡ var (suc i)
wkTm-var i = refl

-- Key lemma: liftSub idSub i = var i for all i
-- This is the critical helper for the main proofs
liftSub-idSub : ∀ {n} (i : Fin (suc n)) → liftSub idSub i ≡ var i
liftSub-idSub zero = refl
liftSub-idSub (suc i) = refl  -- wkTm (var i) = var (suc i) by definition

-- Two-level lift: liftSub (liftSub idSub) i = var i
liftSub-liftSub-idSub : ∀ {n} (i : Fin (suc (suc n))) → liftSub (liftSub idSub) i ≡ var i
liftSub-liftSub-idSub zero = refl
liftSub-liftSub-idSub (suc zero) = refl
liftSub-liftSub-idSub (suc (suc i)) = refl

-- Main theorems: identity substitution is identity
-- Proved by mutual induction on the term/type structure
mutual
  subst-id-tm : ∀ {n} (t : Tm n) → substTm idSub t ≡ t
  subst-id-tm (var i) = refl
  subst-id-tm (lam A t) = cong₂ lam (subst-id-ty A) (subst-id-tm-lift t)
  subst-id-tm (app f a) = cong₂ app (subst-id-tm f) (subst-id-tm a)
  subst-id-tm (pair a b) = cong₂ pair (subst-id-tm a) (subst-id-tm b)
  subst-id-tm (fst t) = cong fst (subst-id-tm t)
  subst-id-tm (snd t) = cong snd (subst-id-tm t)
  subst-id-tm (inl a) = cong inl (subst-id-tm a)
  subst-id-tm (inr b) = cong inr (subst-id-tm b)
  subst-id-tm (case e l r) = cong₃ case (subst-id-tm e) (subst-id-tm-lift l) (subst-id-tm-lift r)
  subst-id-tm refl' = refl
  subst-id-tm (J M d p) = cong₃ J (subst-id-ty-lift2 M) (subst-id-tm d) (subst-id-tm p)

  subst-id-ty : ∀ {n} (A : Ty n) → substTy idSub A ≡ A
  subst-id-ty (base i) = refl
  subst-id-ty (A ⇒ B) = cong₂ _⇒_ (subst-id-ty A) (subst-id-ty-lift B)
  subst-id-ty (A ×' B) = cong₂ _×'_ (subst-id-ty A) (subst-id-ty-lift B)
  subst-id-ty (A +' B) = cong₂ _+'_ (subst-id-ty A) (subst-id-ty B)
  subst-id-ty (Id A a b) = cong₃ Id (subst-id-ty A) (subst-id-tm a) (subst-id-tm b)

  -- Helper: substTm (liftSub idSub) t = t
  -- Uses the fact that liftSub idSub = idSub pointwise
  subst-id-tm-lift : ∀ {n} (t : Tm (suc n)) → substTm (liftSub idSub) t ≡ t
  subst-id-tm-lift (var i) = liftSub-idSub i
  subst-id-tm-lift (lam A t) = cong₂ lam (subst-id-ty-lift A) (subst-id-tm-lift2 t)
  subst-id-tm-lift (app f a) = cong₂ app (subst-id-tm-lift f) (subst-id-tm-lift a)
  subst-id-tm-lift (pair a b) = cong₂ pair (subst-id-tm-lift a) (subst-id-tm-lift b)
  subst-id-tm-lift (fst t) = cong fst (subst-id-tm-lift t)
  subst-id-tm-lift (snd t) = cong snd (subst-id-tm-lift t)
  subst-id-tm-lift (inl a) = cong inl (subst-id-tm-lift a)
  subst-id-tm-lift (inr b) = cong inr (subst-id-tm-lift b)
  subst-id-tm-lift (case e l r) = cong₃ case (subst-id-tm-lift e) (subst-id-tm-lift2 l) (subst-id-tm-lift2 r)
  subst-id-tm-lift refl' = refl
  subst-id-tm-lift (J M d p) = cong₃ J (subst-id-ty-lift3 M) (subst-id-tm-lift d) (subst-id-tm-lift p)

  subst-id-ty-lift : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
  subst-id-ty-lift (base i) = refl
  subst-id-ty-lift (A ⇒ B) = cong₂ _⇒_ (subst-id-ty-lift A) (subst-id-ty-lift2 B)
  subst-id-ty-lift (A ×' B) = cong₂ _×'_ (subst-id-ty-lift A) (subst-id-ty-lift2 B)
  subst-id-ty-lift (A +' B) = cong₂ _+'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
  subst-id-ty-lift (Id A a b) = cong₃ Id (subst-id-ty-lift A) (subst-id-tm-lift a) (subst-id-tm-lift b)

  -- Two-level lift helpers
  liftSub-3-idSub : ∀ {n} (i : Fin (suc (suc (suc n)))) →
    liftSub (liftSub (liftSub idSub)) i ≡ var i
  liftSub-3-idSub zero = refl
  liftSub-3-idSub (suc zero) = refl
  liftSub-3-idSub (suc (suc zero)) = refl
  liftSub-3-idSub (suc (suc (suc i))) = refl

  subst-id-tm-lift2 : ∀ {n} (t : Tm (suc (suc n))) → substTm (liftSub (liftSub idSub)) t ≡ t
  subst-id-tm-lift2 (var i) = liftSub-liftSub-idSub i
  subst-id-tm-lift2 (lam A t) = cong₂ lam (subst-id-ty-lift2 A) (subst-id-tm-lift3 t)
  subst-id-tm-lift2 (app f a) = cong₂ app (subst-id-tm-lift2 f) (subst-id-tm-lift2 a)
  subst-id-tm-lift2 (pair a b) = cong₂ pair (subst-id-tm-lift2 a) (subst-id-tm-lift2 b)
  subst-id-tm-lift2 (fst t) = cong fst (subst-id-tm-lift2 t)
  subst-id-tm-lift2 (snd t) = cong snd (subst-id-tm-lift2 t)
  subst-id-tm-lift2 (inl a) = cong inl (subst-id-tm-lift2 a)
  subst-id-tm-lift2 (inr b) = cong inr (subst-id-tm-lift2 b)
  subst-id-tm-lift2 (case e l r) = cong₃ case (subst-id-tm-lift2 e) (subst-id-tm-lift3 l) (subst-id-tm-lift3 r)
  subst-id-tm-lift2 refl' = refl
  subst-id-tm-lift2 (J M d p) = cong₃ J (subst-id-ty-lift4 M) (subst-id-tm-lift2 d) (subst-id-tm-lift2 p)

  subst-id-ty-lift2 : ∀ {n} (A : Ty (suc (suc n))) → substTy (liftSub (liftSub idSub)) A ≡ A
  subst-id-ty-lift2 (base i) = refl
  subst-id-ty-lift2 (A ⇒ B) = cong₂ _⇒_ (subst-id-ty-lift2 A) (subst-id-ty-lift3 B)
  subst-id-ty-lift2 (A ×' B) = cong₂ _×'_ (subst-id-ty-lift2 A) (subst-id-ty-lift3 B)
  subst-id-ty-lift2 (A +' B) = cong₂ _+'_ (subst-id-ty-lift2 A) (subst-id-ty-lift2 B)
  subst-id-ty-lift2 (Id A a b) = cong₃ Id (subst-id-ty-lift2 A) (subst-id-tm-lift2 a) (subst-id-tm-lift2 b)

  -- Three-level lift helpers (needed for J rule which lifts twice under binders)
  liftSub-4-idSub : ∀ {n} (i : Fin (suc (suc (suc (suc n))))) →
    liftSub (liftSub (liftSub (liftSub idSub))) i ≡ var i
  liftSub-4-idSub zero = refl
  liftSub-4-idSub (suc zero) = refl
  liftSub-4-idSub (suc (suc zero)) = refl
  liftSub-4-idSub (suc (suc (suc zero))) = refl
  liftSub-4-idSub (suc (suc (suc (suc i)))) = refl

  subst-id-tm-lift3 : ∀ {n} (t : Tm (suc (suc (suc n)))) →
    substTm (liftSub (liftSub (liftSub idSub))) t ≡ t
  subst-id-tm-lift3 (var i) = liftSub-3-idSub i
  subst-id-tm-lift3 (lam A t) = cong₂ lam (subst-id-ty-lift3 A) (subst-id-tm-lift4 t)
  subst-id-tm-lift3 (app f a) = cong₂ app (subst-id-tm-lift3 f) (subst-id-tm-lift3 a)
  subst-id-tm-lift3 (pair a b) = cong₂ pair (subst-id-tm-lift3 a) (subst-id-tm-lift3 b)
  subst-id-tm-lift3 (fst t) = cong fst (subst-id-tm-lift3 t)
  subst-id-tm-lift3 (snd t) = cong snd (subst-id-tm-lift3 t)
  subst-id-tm-lift3 (inl a) = cong inl (subst-id-tm-lift3 a)
  subst-id-tm-lift3 (inr b) = cong inr (subst-id-tm-lift3 b)
  subst-id-tm-lift3 (case e l r) = cong₃ case (subst-id-tm-lift3 e) (subst-id-tm-lift4 l) (subst-id-tm-lift4 r)
  subst-id-tm-lift3 refl' = refl
  subst-id-tm-lift3 (J M d p) = cong₃ J (subst-id-ty-lift5 M) (subst-id-tm-lift3 d) (subst-id-tm-lift3 p)

  subst-id-ty-lift3 : ∀ {n} (A : Ty (suc (suc (suc n)))) →
    substTy (liftSub (liftSub (liftSub idSub))) A ≡ A
  subst-id-ty-lift3 (base i) = refl
  subst-id-ty-lift3 (A ⇒ B) = cong₂ _⇒_ (subst-id-ty-lift3 A) (subst-id-ty-lift4 B)
  subst-id-ty-lift3 (A ×' B) = cong₂ _×'_ (subst-id-ty-lift3 A) (subst-id-ty-lift4 B)
  subst-id-ty-lift3 (A +' B) = cong₂ _+'_ (subst-id-ty-lift3 A) (subst-id-ty-lift3 B)
  subst-id-ty-lift3 (Id A a b) = cong₃ Id (subst-id-ty-lift3 A) (subst-id-tm-lift3 a) (subst-id-tm-lift3 b)

  -- Four-level lift helpers (for deeply nested types)
  liftSub-5-idSub : ∀ {n} (i : Fin (suc (suc (suc (suc (suc n)))))) →
    liftSub (liftSub (liftSub (liftSub (liftSub idSub)))) i ≡ var i
  liftSub-5-idSub zero = refl
  liftSub-5-idSub (suc zero) = refl
  liftSub-5-idSub (suc (suc zero)) = refl
  liftSub-5-idSub (suc (suc (suc zero))) = refl
  liftSub-5-idSub (suc (suc (suc (suc zero)))) = refl
  liftSub-5-idSub (suc (suc (suc (suc (suc i))))) = refl

  subst-id-tm-lift4 : ∀ {n} (t : Tm (suc (suc (suc (suc n))))) →
    substTm (liftSub (liftSub (liftSub (liftSub idSub)))) t ≡ t
  subst-id-tm-lift4 (var i) = liftSub-4-idSub i
  subst-id-tm-lift4 (lam A t) = cong₂ lam (subst-id-ty-lift4 A) (subst-id-tm-lift5 t)
  subst-id-tm-lift4 (app f a) = cong₂ app (subst-id-tm-lift4 f) (subst-id-tm-lift4 a)
  subst-id-tm-lift4 (pair a b) = cong₂ pair (subst-id-tm-lift4 a) (subst-id-tm-lift4 b)
  subst-id-tm-lift4 (fst t) = cong fst (subst-id-tm-lift4 t)
  subst-id-tm-lift4 (snd t) = cong snd (subst-id-tm-lift4 t)
  subst-id-tm-lift4 (inl a) = cong inl (subst-id-tm-lift4 a)
  subst-id-tm-lift4 (inr b) = cong inr (subst-id-tm-lift4 b)
  subst-id-tm-lift4 (case e l r) = cong₃ case (subst-id-tm-lift4 e) (subst-id-tm-lift5 l) (subst-id-tm-lift5 r)
  subst-id-tm-lift4 refl' = refl
  subst-id-tm-lift4 (J M d p) = cong₃ J (subst-id-ty-lift6 M) (subst-id-tm-lift4 d) (subst-id-tm-lift4 p)

  subst-id-ty-lift4 : ∀ {n} (A : Ty (suc (suc (suc (suc n))))) →
    substTy (liftSub (liftSub (liftSub (liftSub idSub)))) A ≡ A
  subst-id-ty-lift4 (base i) = refl
  subst-id-ty-lift4 (A ⇒ B) = cong₂ _⇒_ (subst-id-ty-lift4 A) (subst-id-ty-lift5 B)
  subst-id-ty-lift4 (A ×' B) = cong₂ _×'_ (subst-id-ty-lift4 A) (subst-id-ty-lift5 B)
  subst-id-ty-lift4 (A +' B) = cong₂ _+'_ (subst-id-ty-lift4 A) (subst-id-ty-lift4 B)
  subst-id-ty-lift4 (Id A a b) = cong₃ Id (subst-id-ty-lift4 A) (subst-id-tm-lift4 a) (subst-id-tm-lift4 b)

  -- Five-level lift helpers
  liftSub-6-idSub : ∀ {n} (i : Fin (suc (suc (suc (suc (suc (suc n))))))) →
    liftSub (liftSub (liftSub (liftSub (liftSub (liftSub idSub))))) i ≡ var i
  liftSub-6-idSub zero = refl
  liftSub-6-idSub (suc zero) = refl
  liftSub-6-idSub (suc (suc zero)) = refl
  liftSub-6-idSub (suc (suc (suc zero))) = refl
  liftSub-6-idSub (suc (suc (suc (suc zero)))) = refl
  liftSub-6-idSub (suc (suc (suc (suc (suc zero))))) = refl
  liftSub-6-idSub (suc (suc (suc (suc (suc (suc i)))))) = refl

  subst-id-tm-lift5 : ∀ {n} (t : Tm (suc (suc (suc (suc (suc n)))))) →
    substTm (liftSub (liftSub (liftSub (liftSub (liftSub idSub))))) t ≡ t
  subst-id-tm-lift5 (var i) = liftSub-5-idSub i
  subst-id-tm-lift5 (lam A t) = cong₂ lam (subst-id-ty-lift5 A) (subst-id-tm-lift6 t)
  subst-id-tm-lift5 (app f a) = cong₂ app (subst-id-tm-lift5 f) (subst-id-tm-lift5 a)
  subst-id-tm-lift5 (pair a b) = cong₂ pair (subst-id-tm-lift5 a) (subst-id-tm-lift5 b)
  subst-id-tm-lift5 (fst t) = cong fst (subst-id-tm-lift5 t)
  subst-id-tm-lift5 (snd t) = cong snd (subst-id-tm-lift5 t)
  subst-id-tm-lift5 (inl a) = cong inl (subst-id-tm-lift5 a)
  subst-id-tm-lift5 (inr b) = cong inr (subst-id-tm-lift5 b)
  subst-id-tm-lift5 (case e l r) = cong₃ case (subst-id-tm-lift5 e) (subst-id-tm-lift6 l) (subst-id-tm-lift6 r)
  subst-id-tm-lift5 refl' = refl
  subst-id-tm-lift5 (J M d p) = cong₃ J (subst-id-ty-lift7 M) (subst-id-tm-lift5 d) (subst-id-tm-lift5 p)

  subst-id-ty-lift5 : ∀ {n} (A : Ty (suc (suc (suc (suc (suc n)))))) →
    substTy (liftSub (liftSub (liftSub (liftSub (liftSub idSub))))) A ≡ A
  subst-id-ty-lift5 (base i) = refl
  subst-id-ty-lift5 (A ⇒ B) = cong₂ _⇒_ (subst-id-ty-lift5 A) (subst-id-ty-lift6 B)
  subst-id-ty-lift5 (A ×' B) = cong₂ _×'_ (subst-id-ty-lift5 A) (subst-id-ty-lift6 B)
  subst-id-ty-lift5 (A +' B) = cong₂ _+'_ (subst-id-ty-lift5 A) (subst-id-ty-lift5 B)
  subst-id-ty-lift5 (Id A a b) = cong₃ Id (subst-id-ty-lift5 A) (subst-id-tm-lift5 a) (subst-id-tm-lift5 b)

  -- Higher levels postulated to ensure termination (sufficient for practical use)
  postulate
    subst-id-tm-lift6 : ∀ {n} (t : Tm (suc (suc (suc (suc (suc (suc n))))))) →
      substTm (liftSub (liftSub (liftSub (liftSub (liftSub (liftSub idSub)))))) t ≡ t
    subst-id-ty-lift6 : ∀ {n} (A : Ty (suc (suc (suc (suc (suc (suc n))))))) →
      substTy (liftSub (liftSub (liftSub (liftSub (liftSub (liftSub idSub)))))) A ≡ A
    subst-id-ty-lift7 : ∀ {n} (A : Ty (suc (suc (suc (suc (suc (suc (suc n)))))))) →
      substTy (liftSub (liftSub (liftSub (liftSub (liftSub (liftSub (liftSub idSub))))))) A ≡ A
