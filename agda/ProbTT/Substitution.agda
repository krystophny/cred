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

-- Apply renaming to terms
renTm : ∀ {m n} → Ren m n → Tm m → Tm n
renTy : ∀ {m n} → Ren m n → Ty m → Ty n

renTm ρ (var i)       = var (ρ i)
renTm ρ (lam A t)     = lam (renTy ρ A) (renTm (liftRen ρ) t)
renTm ρ (app f a)     = app (renTm ρ f) (renTm ρ a)
renTm ρ (pair a b)    = pair (renTm ρ a) (renTm ρ b)
renTm ρ (fst t)       = fst (renTm ρ t)
renTm ρ (snd t)       = snd (renTm ρ t)
renTm ρ (inl a)       = inl (renTm ρ a)
renTm ρ (inr b)       = inr (renTm ρ b)
renTm ρ (case e l r)  = case (renTm ρ e) (renTm (liftRen ρ) l) (renTm (liftRen ρ) r)
renTm ρ star          = star
renTm ρ (abort A e)   = abort (renTy ρ A) (renTm ρ e)
renTm ρ refl'         = refl'
renTm ρ (J M d p)     = J (renTy (liftRen (liftRen ρ)) M) (renTm ρ d) (renTm ρ p)

renTy ρ (base i)   = base i
renTy ρ (A ⇒ B)    = renTy ρ A ⇒ renTy (liftRen ρ) B
renTy ρ (A ×' B)   = renTy ρ A ×' renTy (liftRen ρ) B
renTy ρ (A +' B)   = renTy ρ A +' renTy ρ B
renTy ρ 𝟙'         = 𝟙'
renTy ρ 𝟘'         = 𝟘'
renTy ρ (Id A a b) = Id (renTy ρ A) (renTm ρ a) (renTm ρ b)

-- Weakening: add unused variable at position 0
wkTm : ∀ {n} → Tm n → Tm (suc n)
wkTm = renTm suc

wkTy : ∀ {n} → Ty n → Ty (suc n)
wkTy = renTy suc

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

-- Apply substitution to terms
substTm : ∀ {m n} → Sub m n → Tm m → Tm n
substTy : ∀ {m n} → Sub m n → Ty m → Ty n

substTm σ (var i)       = σ i
substTm σ (lam A t)     = lam (substTy σ A) (substTm (liftSub σ) t)
substTm σ (app f a)     = app (substTm σ f) (substTm σ a)
substTm σ (pair a b)    = pair (substTm σ a) (substTm σ b)
substTm σ (fst t)       = fst (substTm σ t)
substTm σ (snd t)       = snd (substTm σ t)
substTm σ (inl a)       = inl (substTm σ a)
substTm σ (inr b)       = inr (substTm σ b)
substTm σ (case e l r)  = case (substTm σ e) (substTm (liftSub σ) l) (substTm (liftSub σ) r)
substTm σ star          = star
substTm σ (abort A e)   = abort (substTy σ A) (substTm σ e)
substTm σ refl'         = refl'
substTm σ (J M d p)     = J (substTy (liftSub (liftSub σ)) M) (substTm σ d) (substTm σ p)

substTy σ (base i)   = base i
substTy σ (A ⇒ B)    = substTy σ A ⇒ substTy (liftSub σ) B
substTy σ (A ×' B)   = substTy σ A ×' substTy (liftSub σ) B
substTy σ (A +' B)   = substTy σ A +' substTy σ B
substTy σ 𝟙'         = 𝟙'
substTy σ 𝟘'         = 𝟘'
substTy σ (Id A a b) = Id (substTy σ A) (substTm σ a) (substTm σ b)

-- Convenient notation for single substitution
_[_] : ∀ {n} → Tm (suc n) → Tm n → Tm n
t [ a ] = substTm (singleSub a) t

_[_]ₜ : ∀ {n} → Ty (suc n) → Tm n → Ty n
A [ a ]ₜ = substTy (singleSub a) A

-- Key lemma: substituting var gives the term
subst-var : ∀ {n} (t : Tm n) → var zero [ t ] ≡ t
subst-var t = refl

-- Identity substitution is identity
subst-id-tm : ∀ {n} (t : Tm n) → substTm idSub t ≡ t
subst-id-ty : ∀ {n} (A : Ty n) → substTy idSub A ≡ A

-- Helper: liftSub of idSub is idSub
lift-id : ∀ {n} (i : Fin (suc n)) → liftSub idSub i ≡ var i
lift-id zero    = refl
lift-id (suc i) = refl

subst-id-tm (var i)       = refl
subst-id-tm (lam A t)     = cong₂ lam (subst-id-ty A) (subst-id-tm-lift t)
  where
    subst-id-tm-lift : ∀ {n} (t : Tm (suc n)) → substTm (liftSub idSub) t ≡ t
    subst-id-tm-lift t = helper t
      where
        helper : ∀ {n} (t : Tm (suc n)) → substTm (liftSub idSub) t ≡ t
        helper (var zero)    = refl
        helper (var (suc i)) = refl
        helper (lam A s)     = cong₂ lam (helper-ty A) (helper s)
          where
            helper-ty : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
            helper-ty (base i)   = refl
            helper-ty (A ⇒ B)    = cong₂ _⇒_ (helper-ty A) (helper-ty B)
            helper-ty (A ×' B)   = cong₂ _×'_ (helper-ty A) (helper-ty B)
            helper-ty (A +' B)   = cong₂ _+'_ (helper-ty A) (helper-ty B)
            helper-ty 𝟙'         = refl
            helper-ty 𝟘'         = refl
            helper-ty (Id A a b) = cong₃ Id (helper-ty A) (helper a) (helper b)
              where
                cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                        x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
                cong₃ f refl refl refl = refl
        helper (app f a)     = cong₂ app (helper f) (helper a)
        helper (pair a b)    = cong₂ pair (helper a) (helper b)
        helper (fst t)       = cong fst (helper t)
        helper (snd t)       = cong snd (helper t)
        helper (inl a)       = cong inl (helper a)
        helper (inr b)       = cong inr (helper b)
        helper (case e l r)  = cong₃ case (helper e) (helper l) (helper r)
          where
            cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                    x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
            cong₃ f refl refl refl = refl
        helper star          = refl
        helper (abort A e)   = cong₂ abort (helper-ty A) (helper e)
          where
            helper-ty : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
            helper-ty (base i)   = refl
            helper-ty (A ⇒ B)    = cong₂ _⇒_ (helper-ty A) (helper-ty B)
            helper-ty (A ×' B)   = cong₂ _×'_ (helper-ty A) (helper-ty B)
            helper-ty (A +' B)   = cong₂ _+'_ (helper-ty A) (helper-ty B)
            helper-ty 𝟙'         = refl
            helper-ty 𝟘'         = refl
            helper-ty (Id A a b) = cong₃ Id (helper-ty A) (helper a) (helper b)
              where
                cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                        x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
                cong₃ f refl refl refl = refl
        helper refl'         = refl
        helper (J M d p)     = cong₃ J (helper-ty M) (helper d) (helper p)
          where
            helper-ty : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
            helper-ty (base i)   = refl
            helper-ty (A ⇒ B)    = cong₂ _⇒_ (helper-ty A) (helper-ty B)
            helper-ty (A ×' B)   = cong₂ _×'_ (helper-ty A) (helper-ty B)
            helper-ty (A +' B)   = cong₂ _+'_ (helper-ty A) (helper-ty B)
            helper-ty 𝟙'         = refl
            helper-ty 𝟘'         = refl
            helper-ty (Id A a b) = cong₃ Id (helper-ty A) (helper a) (helper b)
              where
                cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                        x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
                cong₃ f refl refl refl = refl
            cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                    x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
            cong₃ f refl refl refl = refl
subst-id-tm (app f a)     = cong₂ app (subst-id-tm f) (subst-id-tm a)
subst-id-tm (pair a b)    = cong₂ pair (subst-id-tm a) (subst-id-tm b)
subst-id-tm (fst t)       = cong fst (subst-id-tm t)
subst-id-tm (snd t)       = cong snd (subst-id-tm t)
subst-id-tm (inl a)       = cong inl (subst-id-tm a)
subst-id-tm (inr b)       = cong inr (subst-id-tm b)
subst-id-tm (case e l r)  = cong₃ case (subst-id-tm e) (subst-id-tm-lift l) (subst-id-tm-lift r)
  where
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
    cong₃ f refl refl refl = refl

    subst-id-tm-lift : ∀ {n} (t : Tm (suc n)) → substTm (liftSub idSub) t ≡ t
    subst-id-tm-lift (var zero)    = refl
    subst-id-tm-lift (var (suc i)) = refl
    subst-id-tm-lift (lam A s)     = cong₂ lam (subst-id-ty-lift A) (subst-id-tm-lift s)
      where
        subst-id-ty-lift : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
        subst-id-ty-lift (base i)   = refl
        subst-id-ty-lift (A ⇒ B)    = cong₂ _⇒_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift (A ×' B)   = cong₂ _×'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift (A +' B)   = cong₂ _+'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift 𝟙'         = refl
        subst-id-ty-lift 𝟘'         = refl
        subst-id-ty-lift (Id A a b) = cong₃ Id (subst-id-ty-lift A) (subst-id-tm-lift a) (subst-id-tm-lift b)
    subst-id-tm-lift (app f a)     = cong₂ app (subst-id-tm-lift f) (subst-id-tm-lift a)
    subst-id-tm-lift (pair a b)    = cong₂ pair (subst-id-tm-lift a) (subst-id-tm-lift b)
    subst-id-tm-lift (fst t)       = cong fst (subst-id-tm-lift t)
    subst-id-tm-lift (snd t)       = cong snd (subst-id-tm-lift t)
    subst-id-tm-lift (inl a)       = cong inl (subst-id-tm-lift a)
    subst-id-tm-lift (inr b)       = cong inr (subst-id-tm-lift b)
    subst-id-tm-lift (case e l r)  = cong₃ case (subst-id-tm-lift e) (subst-id-tm-lift l) (subst-id-tm-lift r)
    subst-id-tm-lift star          = refl
    subst-id-tm-lift (abort A e)   = cong₂ abort (subst-id-ty-lift A) (subst-id-tm-lift e)
      where
        subst-id-ty-lift : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
        subst-id-ty-lift (base i)   = refl
        subst-id-ty-lift (A ⇒ B)    = cong₂ _⇒_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift (A ×' B)   = cong₂ _×'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift (A +' B)   = cong₂ _+'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift 𝟙'         = refl
        subst-id-ty-lift 𝟘'         = refl
        subst-id-ty-lift (Id A a b) = cong₃ Id (subst-id-ty-lift A) (subst-id-tm-lift a) (subst-id-tm-lift b)
    subst-id-tm-lift refl'         = refl
    subst-id-tm-lift (J M d p)     = cong₃ J (subst-id-ty-lift M) (subst-id-tm-lift d) (subst-id-tm-lift p)
      where
        subst-id-ty-lift : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
        subst-id-ty-lift (base i)   = refl
        subst-id-ty-lift (A ⇒ B)    = cong₂ _⇒_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift (A ×' B)   = cong₂ _×'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift (A +' B)   = cong₂ _+'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
        subst-id-ty-lift 𝟙'         = refl
        subst-id-ty-lift 𝟘'         = refl
        subst-id-ty-lift (Id A a b) = cong₃ Id (subst-id-ty-lift A) (subst-id-tm-lift a) (subst-id-tm-lift b)
subst-id-tm star          = refl
subst-id-tm (abort A e)   = cong₂ abort (subst-id-ty A) (subst-id-tm e)
subst-id-tm refl'         = refl
subst-id-tm (J M d p)     = cong₃ J (subst-id-ty-lift2 M) (subst-id-tm d) (subst-id-tm p)
  where
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
    cong₃ f refl refl refl = refl

    subst-id-tm-lift2 : ∀ {n} (t : Tm (suc (suc n))) → substTm (liftSub (liftSub idSub)) t ≡ t
    subst-id-ty-lift2 : ∀ {n} (A : Ty (suc (suc n))) → substTy (liftSub (liftSub idSub)) A ≡ A

    subst-id-tm-lift2 (var zero)       = refl
    subst-id-tm-lift2 (var (suc zero)) = refl
    subst-id-tm-lift2 (var (suc (suc i))) = refl
    subst-id-tm-lift2 (lam A s)     = cong₂ lam (subst-id-ty-lift2 A) (subst-id-tm-lift2 s)
    subst-id-tm-lift2 (app f a)     = cong₂ app (subst-id-tm-lift2 f) (subst-id-tm-lift2 a)
    subst-id-tm-lift2 (pair a b)    = cong₂ pair (subst-id-tm-lift2 a) (subst-id-tm-lift2 b)
    subst-id-tm-lift2 (fst t)       = cong fst (subst-id-tm-lift2 t)
    subst-id-tm-lift2 (snd t)       = cong snd (subst-id-tm-lift2 t)
    subst-id-tm-lift2 (inl a)       = cong inl (subst-id-tm-lift2 a)
    subst-id-tm-lift2 (inr b)       = cong inr (subst-id-tm-lift2 b)
    subst-id-tm-lift2 (case e l r)  = cong₃ case (subst-id-tm-lift2 e) (subst-id-tm-lift2 l) (subst-id-tm-lift2 r)
    subst-id-tm-lift2 star          = refl
    subst-id-tm-lift2 (abort A e)   = cong₂ abort (subst-id-ty-lift2 A) (subst-id-tm-lift2 e)
    subst-id-tm-lift2 refl'         = refl
    subst-id-tm-lift2 (J M d p)     = cong₃ J (subst-id-ty-lift2 M) (subst-id-tm-lift2 d) (subst-id-tm-lift2 p)

    subst-id-ty-lift2 (base i)   = refl
    subst-id-ty-lift2 (A ⇒ B)    = cong₂ _⇒_ (subst-id-ty-lift2 A) (subst-id-ty-lift2 B)
    subst-id-ty-lift2 (A ×' B)   = cong₂ _×'_ (subst-id-ty-lift2 A) (subst-id-ty-lift2 B)
    subst-id-ty-lift2 (A +' B)   = cong₂ _+'_ (subst-id-ty-lift2 A) (subst-id-ty-lift2 B)
    subst-id-ty-lift2 𝟙'         = refl
    subst-id-ty-lift2 𝟘'         = refl
    subst-id-ty-lift2 (Id A a b) = cong₃ Id (subst-id-ty-lift2 A) (subst-id-tm-lift2 a) (subst-id-tm-lift2 b)

subst-id-ty (base i)   = refl
subst-id-ty (A ⇒ B)    = cong₂ _⇒_ (subst-id-ty A) (subst-id-ty-lift B)
  where
    subst-id-ty-lift : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
    subst-id-tm-lift : ∀ {n} (t : Tm (suc n)) → substTm (liftSub idSub) t ≡ t

    subst-id-tm-lift (var zero)    = refl
    subst-id-tm-lift (var (suc i)) = refl
    subst-id-tm-lift (lam A s)     = cong₂ lam (subst-id-ty-lift A) (subst-id-tm-lift s)
    subst-id-tm-lift (app f a)     = cong₂ app (subst-id-tm-lift f) (subst-id-tm-lift a)
    subst-id-tm-lift (pair a b)    = cong₂ pair (subst-id-tm-lift a) (subst-id-tm-lift b)
    subst-id-tm-lift (fst t)       = cong fst (subst-id-tm-lift t)
    subst-id-tm-lift (snd t)       = cong snd (subst-id-tm-lift t)
    subst-id-tm-lift (inl a)       = cong inl (subst-id-tm-lift a)
    subst-id-tm-lift (inr b)       = cong inr (subst-id-tm-lift b)
    subst-id-tm-lift (case e l r)  = cong₃ case (subst-id-tm-lift e) (subst-id-tm-lift l) (subst-id-tm-lift r)
      where
        cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
        cong₃ f refl refl refl = refl
    subst-id-tm-lift star          = refl
    subst-id-tm-lift (abort A e)   = cong₂ abort (subst-id-ty-lift A) (subst-id-tm-lift e)
    subst-id-tm-lift refl'         = refl
    subst-id-tm-lift (J M d p)     = cong₃ J (subst-id-ty-lift M) (subst-id-tm-lift d) (subst-id-tm-lift p)
      where
        cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
        cong₃ f refl refl refl = refl

    subst-id-ty-lift (base i)   = refl
    subst-id-ty-lift (A ⇒ B)    = cong₂ _⇒_ (subst-id-ty-lift A) (subst-id-ty-lift B)
    subst-id-ty-lift (A ×' B)   = cong₂ _×'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
    subst-id-ty-lift (A +' B)   = cong₂ _+'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
    subst-id-ty-lift 𝟙'         = refl
    subst-id-ty-lift 𝟘'         = refl
    subst-id-ty-lift (Id A a b) = cong₃ Id (subst-id-ty-lift A) (subst-id-tm-lift a) (subst-id-tm-lift b)
      where
        cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
        cong₃ f refl refl refl = refl
subst-id-ty (A ×' B)   = cong₂ _×'_ (subst-id-ty A) (subst-id-ty-lift B)
  where
    subst-id-ty-lift : ∀ {n} (A : Ty (suc n)) → substTy (liftSub idSub) A ≡ A
    subst-id-tm-lift : ∀ {n} (t : Tm (suc n)) → substTm (liftSub idSub) t ≡ t

    subst-id-tm-lift (var zero)    = refl
    subst-id-tm-lift (var (suc i)) = refl
    subst-id-tm-lift (lam A s)     = cong₂ lam (subst-id-ty-lift A) (subst-id-tm-lift s)
    subst-id-tm-lift (app f a)     = cong₂ app (subst-id-tm-lift f) (subst-id-tm-lift a)
    subst-id-tm-lift (pair a b)    = cong₂ pair (subst-id-tm-lift a) (subst-id-tm-lift b)
    subst-id-tm-lift (fst t)       = cong fst (subst-id-tm-lift t)
    subst-id-tm-lift (snd t)       = cong snd (subst-id-tm-lift t)
    subst-id-tm-lift (inl a)       = cong inl (subst-id-tm-lift a)
    subst-id-tm-lift (inr b)       = cong inr (subst-id-tm-lift b)
    subst-id-tm-lift (case e l r)  = cong₃ case (subst-id-tm-lift e) (subst-id-tm-lift l) (subst-id-tm-lift r)
      where
        cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
        cong₃ f refl refl refl = refl
    subst-id-tm-lift star          = refl
    subst-id-tm-lift (abort A e)   = cong₂ abort (subst-id-ty-lift A) (subst-id-tm-lift e)
    subst-id-tm-lift refl'         = refl
    subst-id-tm-lift (J M d p)     = cong₃ J (subst-id-ty-lift M) (subst-id-tm-lift d) (subst-id-tm-lift p)
      where
        cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
        cong₃ f refl refl refl = refl

    subst-id-ty-lift (base i)   = refl
    subst-id-ty-lift (A ⇒ B)    = cong₂ _⇒_ (subst-id-ty-lift A) (subst-id-ty-lift B)
    subst-id-ty-lift (A ×' B)   = cong₂ _×'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
    subst-id-ty-lift (A +' B)   = cong₂ _+'_ (subst-id-ty-lift A) (subst-id-ty-lift B)
    subst-id-ty-lift 𝟙'         = refl
    subst-id-ty-lift 𝟘'         = refl
    subst-id-ty-lift (Id A a b) = cong₃ Id (subst-id-ty-lift A) (subst-id-tm-lift a) (subst-id-tm-lift b)
      where
        cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
                x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
        cong₃ f refl refl refl = refl
subst-id-ty (A +' B)   = cong₂ _+'_ (subst-id-ty A) (subst-id-ty B)
subst-id-ty 𝟙'         = refl
subst-id-ty 𝟘'         = refl
subst-id-ty (Id A a b) = cong₃ Id (subst-id-ty A) (subst-id-tm a) (subst-id-tm b)
  where
    cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x₁ x₂ y₁ y₂ z₁ z₂} →
            x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → f x₁ y₁ z₁ ≡ f x₂ y₂ z₂
    cong₃ f refl refl refl = refl
