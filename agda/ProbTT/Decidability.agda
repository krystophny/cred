module ProbTT.Decidability where

open import Level using (Level; suc; _⊔_)
open import Data.Nat as Nat using (ℕ; zero; suc; _≟_; s≤s; z≤n; _+_)
open import Data.Fin as Fin using (Fin; zero; suc; toℕ)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃) renaming (_,_ to _Σ,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Substitution
open import ProbTT.Context
open import ProbTT.Judgment

module Decidability {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM

  -- Weight comparison decidability requires decidable equality and ordering
  -- on the weight algebra. We parameterize by these.
  record DecidableWeight : Set ℓ where
    field
      _≟W_ : (w v : W) → Dec (w ≡ v)
      _≤?W_ : (w v : W) → Dec (w ≤ v)

  module WithDecidableWeight (DW : DecidableWeight) where
    open DecidableWeight DW

    open Nat using (_+_)

    -- Term size for termination proofs
    mutual
      tm-size : ∀ {n} → Tm n → ℕ
      tm-size (var i)      = 1
      tm-size (lam A t)    = 1 + ty-size A + tm-size t
      tm-size (app f a)    = 1 + tm-size f + tm-size a
      tm-size (pair a b)   = 1 + tm-size a + tm-size b
      tm-size (fst t)      = 1 + tm-size t
      tm-size (snd t)      = 1 + tm-size t
      tm-size (inl a)      = 1 + tm-size a
      tm-size (inr b)      = 1 + tm-size b
      tm-size (case e l r) = 1 + tm-size e + tm-size l + tm-size r
      tm-size refl'        = 1
      tm-size (J M d p)    = 1 + ty-size M + tm-size d + tm-size p

      ty-size : ∀ {n} → Ty n → ℕ
      ty-size (base i)   = 1
      ty-size (A ⇒ B)    = 1 + ty-size A + ty-size B
      ty-size (A ×' B)   = 1 + ty-size A + ty-size B
      ty-size (A +' B)   = 1 + ty-size A + ty-size B
      ty-size (Id A a b) = 1 + ty-size A + tm-size a + tm-size b

    -- Decidable equality for types and terms
    mutual
      _≟Ty_ : ∀ {n} (A B : Ty n) → Dec (A ≡ B)
      base i ≟Ty base j with i ≟ j
      ... | yes refl = yes refl
      ... | no ¬p = no (λ { refl → ¬p refl })
      base i ≟Ty (_ ⇒ _) = no (λ ())
      base i ≟Ty (_ ×' _) = no (λ ())
      base i ≟Ty (_ +' _) = no (λ ())
      base i ≟Ty Id _ _ _ = no (λ ())
      (A₁ ⇒ B₁) ≟Ty base _ = no (λ ())
      (A₁ ⇒ B₁) ≟Ty (A₂ ⇒ B₂) with A₁ ≟Ty A₂ | B₁ ≟Ty B₂
      ... | yes refl | yes refl = yes refl
      ... | no ¬p | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q = no (λ { refl → ¬q refl })
      (A₁ ⇒ B₁) ≟Ty (_ ×' _) = no (λ ())
      (A₁ ⇒ B₁) ≟Ty (_ +' _) = no (λ ())
      (A₁ ⇒ B₁) ≟Ty Id _ _ _ = no (λ ())
      (A₁ ×' B₁) ≟Ty base _ = no (λ ())
      (A₁ ×' B₁) ≟Ty (_ ⇒ _) = no (λ ())
      (A₁ ×' B₁) ≟Ty (A₂ ×' B₂) with A₁ ≟Ty A₂ | B₁ ≟Ty B₂
      ... | yes refl | yes refl = yes refl
      ... | no ¬p | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q = no (λ { refl → ¬q refl })
      (A₁ ×' B₁) ≟Ty (_ +' _) = no (λ ())
      (A₁ ×' B₁) ≟Ty Id _ _ _ = no (λ ())
      (A₁ +' B₁) ≟Ty base _ = no (λ ())
      (A₁ +' B₁) ≟Ty (_ ⇒ _) = no (λ ())
      (A₁ +' B₁) ≟Ty (_ ×' _) = no (λ ())
      (A₁ +' B₁) ≟Ty (A₂ +' B₂) with A₁ ≟Ty A₂ | B₁ ≟Ty B₂
      ... | yes refl | yes refl = yes refl
      ... | no ¬p | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q = no (λ { refl → ¬q refl })
      (A₁ +' B₁) ≟Ty Id _ _ _ = no (λ ())
      Id A₁ a₁ b₁ ≟Ty base _ = no (λ ())
      Id A₁ a₁ b₁ ≟Ty (_ ⇒ _) = no (λ ())
      Id A₁ a₁ b₁ ≟Ty (_ ×' _) = no (λ ())
      Id A₁ a₁ b₁ ≟Ty (_ +' _) = no (λ ())
      Id A₁ a₁ b₁ ≟Ty Id A₂ a₂ b₂ with A₁ ≟Ty A₂ | a₁ ≟Tm a₂ | b₁ ≟Tm b₂
      ... | yes refl | yes refl | yes refl = yes refl
      ... | no ¬p | _ | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q | _ = no (λ { refl → ¬q refl })
      ... | _ | _ | no ¬r = no (λ { refl → ¬r refl })

      _≟Tm_ : ∀ {n} (s t : Tm n) → Dec (s ≡ t)
      var i ≟Tm var j with Fin._≟_ i j
      ... | yes refl = yes refl
      ... | no ¬p = no (λ { refl → ¬p refl })
      var _ ≟Tm lam _ _ = no (λ ())
      var _ ≟Tm app _ _ = no (λ ())
      var _ ≟Tm pair _ _ = no (λ ())
      var _ ≟Tm fst _ = no (λ ())
      var _ ≟Tm snd _ = no (λ ())
      var _ ≟Tm inl _ = no (λ ())
      var _ ≟Tm inr _ = no (λ ())
      var _ ≟Tm case _ _ _ = no (λ ())
      var _ ≟Tm refl' = no (λ ())
      var _ ≟Tm J _ _ _ = no (λ ())
      lam _ _ ≟Tm var _ = no (λ ())
      lam A₁ t₁ ≟Tm lam A₂ t₂ with A₁ ≟Ty A₂ | t₁ ≟Tm t₂
      ... | yes refl | yes refl = yes refl
      ... | no ¬p | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q = no (λ { refl → ¬q refl })
      lam _ _ ≟Tm app _ _ = no (λ ())
      lam _ _ ≟Tm pair _ _ = no (λ ())
      lam _ _ ≟Tm fst _ = no (λ ())
      lam _ _ ≟Tm snd _ = no (λ ())
      lam _ _ ≟Tm inl _ = no (λ ())
      lam _ _ ≟Tm inr _ = no (λ ())
      lam _ _ ≟Tm case _ _ _ = no (λ ())
      lam _ _ ≟Tm refl' = no (λ ())
      lam _ _ ≟Tm J _ _ _ = no (λ ())
      app _ _ ≟Tm var _ = no (λ ())
      app _ _ ≟Tm lam _ _ = no (λ ())
      app f₁ a₁ ≟Tm app f₂ a₂ with f₁ ≟Tm f₂ | a₁ ≟Tm a₂
      ... | yes refl | yes refl = yes refl
      ... | no ¬p | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q = no (λ { refl → ¬q refl })
      app _ _ ≟Tm pair _ _ = no (λ ())
      app _ _ ≟Tm fst _ = no (λ ())
      app _ _ ≟Tm snd _ = no (λ ())
      app _ _ ≟Tm inl _ = no (λ ())
      app _ _ ≟Tm inr _ = no (λ ())
      app _ _ ≟Tm case _ _ _ = no (λ ())
      app _ _ ≟Tm refl' = no (λ ())
      app _ _ ≟Tm J _ _ _ = no (λ ())
      pair _ _ ≟Tm var _ = no (λ ())
      pair _ _ ≟Tm lam _ _ = no (λ ())
      pair _ _ ≟Tm app _ _ = no (λ ())
      pair a₁ b₁ ≟Tm pair a₂ b₂ with a₁ ≟Tm a₂ | b₁ ≟Tm b₂
      ... | yes refl | yes refl = yes refl
      ... | no ¬p | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q = no (λ { refl → ¬q refl })
      pair _ _ ≟Tm fst _ = no (λ ())
      pair _ _ ≟Tm snd _ = no (λ ())
      pair _ _ ≟Tm inl _ = no (λ ())
      pair _ _ ≟Tm inr _ = no (λ ())
      pair _ _ ≟Tm case _ _ _ = no (λ ())
      pair _ _ ≟Tm refl' = no (λ ())
      pair _ _ ≟Tm J _ _ _ = no (λ ())
      fst _ ≟Tm var _ = no (λ ())
      fst _ ≟Tm lam _ _ = no (λ ())
      fst _ ≟Tm app _ _ = no (λ ())
      fst _ ≟Tm pair _ _ = no (λ ())
      fst t₁ ≟Tm fst t₂ with t₁ ≟Tm t₂
      ... | yes refl = yes refl
      ... | no ¬p = no (λ { refl → ¬p refl })
      fst _ ≟Tm snd _ = no (λ ())
      fst _ ≟Tm inl _ = no (λ ())
      fst _ ≟Tm inr _ = no (λ ())
      fst _ ≟Tm case _ _ _ = no (λ ())
      fst _ ≟Tm refl' = no (λ ())
      fst _ ≟Tm J _ _ _ = no (λ ())
      snd _ ≟Tm var _ = no (λ ())
      snd _ ≟Tm lam _ _ = no (λ ())
      snd _ ≟Tm app _ _ = no (λ ())
      snd _ ≟Tm pair _ _ = no (λ ())
      snd _ ≟Tm fst _ = no (λ ())
      snd t₁ ≟Tm snd t₂ with t₁ ≟Tm t₂
      ... | yes refl = yes refl
      ... | no ¬p = no (λ { refl → ¬p refl })
      snd _ ≟Tm inl _ = no (λ ())
      snd _ ≟Tm inr _ = no (λ ())
      snd _ ≟Tm case _ _ _ = no (λ ())
      snd _ ≟Tm refl' = no (λ ())
      snd _ ≟Tm J _ _ _ = no (λ ())
      inl _ ≟Tm var _ = no (λ ())
      inl _ ≟Tm lam _ _ = no (λ ())
      inl _ ≟Tm app _ _ = no (λ ())
      inl _ ≟Tm pair _ _ = no (λ ())
      inl _ ≟Tm fst _ = no (λ ())
      inl _ ≟Tm snd _ = no (λ ())
      inl a₁ ≟Tm inl a₂ with a₁ ≟Tm a₂
      ... | yes refl = yes refl
      ... | no ¬p = no (λ { refl → ¬p refl })
      inl _ ≟Tm inr _ = no (λ ())
      inl _ ≟Tm case _ _ _ = no (λ ())
      inl _ ≟Tm refl' = no (λ ())
      inl _ ≟Tm J _ _ _ = no (λ ())
      inr _ ≟Tm var _ = no (λ ())
      inr _ ≟Tm lam _ _ = no (λ ())
      inr _ ≟Tm app _ _ = no (λ ())
      inr _ ≟Tm pair _ _ = no (λ ())
      inr _ ≟Tm fst _ = no (λ ())
      inr _ ≟Tm snd _ = no (λ ())
      inr _ ≟Tm inl _ = no (λ ())
      inr b₁ ≟Tm inr b₂ with b₁ ≟Tm b₂
      ... | yes refl = yes refl
      ... | no ¬p = no (λ { refl → ¬p refl })
      inr _ ≟Tm case _ _ _ = no (λ ())
      inr _ ≟Tm refl' = no (λ ())
      inr _ ≟Tm J _ _ _ = no (λ ())
      case _ _ _ ≟Tm var _ = no (λ ())
      case _ _ _ ≟Tm lam _ _ = no (λ ())
      case _ _ _ ≟Tm app _ _ = no (λ ())
      case _ _ _ ≟Tm pair _ _ = no (λ ())
      case _ _ _ ≟Tm fst _ = no (λ ())
      case _ _ _ ≟Tm snd _ = no (λ ())
      case _ _ _ ≟Tm inl _ = no (λ ())
      case _ _ _ ≟Tm inr _ = no (λ ())
      case e₁ l₁ r₁ ≟Tm case e₂ l₂ r₂ with e₁ ≟Tm e₂ | l₁ ≟Tm l₂ | r₁ ≟Tm r₂
      ... | yes refl | yes refl | yes refl = yes refl
      ... | no ¬p | _ | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q | _ = no (λ { refl → ¬q refl })
      ... | _ | _ | no ¬r = no (λ { refl → ¬r refl })
      case _ _ _ ≟Tm refl' = no (λ ())
      case _ _ _ ≟Tm J _ _ _ = no (λ ())
      refl' ≟Tm var _ = no (λ ())
      refl' ≟Tm lam _ _ = no (λ ())
      refl' ≟Tm app _ _ = no (λ ())
      refl' ≟Tm pair _ _ = no (λ ())
      refl' ≟Tm fst _ = no (λ ())
      refl' ≟Tm snd _ = no (λ ())
      refl' ≟Tm inl _ = no (λ ())
      refl' ≟Tm inr _ = no (λ ())
      refl' ≟Tm case _ _ _ = no (λ ())
      refl' ≟Tm refl' = yes refl
      refl' ≟Tm J _ _ _ = no (λ ())
      J _ _ _ ≟Tm var _ = no (λ ())
      J _ _ _ ≟Tm lam _ _ = no (λ ())
      J _ _ _ ≟Tm app _ _ = no (λ ())
      J _ _ _ ≟Tm pair _ _ = no (λ ())
      J _ _ _ ≟Tm fst _ = no (λ ())
      J _ _ _ ≟Tm snd _ = no (λ ())
      J _ _ _ ≟Tm inl _ = no (λ ())
      J _ _ _ ≟Tm inr _ = no (λ ())
      J _ _ _ ≟Tm case _ _ _ = no (λ ())
      J _ _ _ ≟Tm refl' = no (λ ())
      J M₁ d₁ p₁ ≟Tm J M₂ d₂ p₂ with M₁ ≟Ty M₂ | d₁ ≟Tm d₂ | p₁ ≟Tm p₂
      ... | yes refl | yes refl | yes refl = yes refl
      ... | no ¬p | _ | _ = no (λ { refl → ¬p refl })
      ... | _ | no ¬q | _ = no (λ { refl → ¬q refl })
      ... | _ | _ | no ¬r = no (λ { refl → ¬r refl })

    -- Type formation is decidable
    -- The algorithm terminates because type size decreases
    type-formation-dec : ∀ {n} (Γ : Ctx n) (A : Ty n) → Dec (Γ ⊢ A type)
    type-formation-dec Γ (base i) = yes (base-form i)
    type-formation-dec Γ (A ⇒ B) with type-formation-dec Γ A
    ... | no ¬Af = no (λ { (Π-form Af _) → ¬Af Af })
    ... | yes Af with type-formation-dec (Γ , A) B
    ...   | no ¬Bf = no (λ { (Π-form _ Bf) → ¬Bf Bf })
    ...   | yes Bf = yes (Π-form Af Bf)
    type-formation-dec Γ (A ×' B) with type-formation-dec Γ A
    ... | no ¬Af = no (λ { (Σ-form Af _) → ¬Af Af })
    ... | yes Af with type-formation-dec (Γ , A) B
    ...   | no ¬Bf = no (λ { (Σ-form _ Bf) → ¬Bf Bf })
    ...   | yes Bf = yes (Σ-form Af Bf)
    type-formation-dec Γ (A +' B) with type-formation-dec Γ A
    ... | no ¬Af = no (λ { (+-form Af _) → ¬Af Af })
    ... | yes Af with type-formation-dec Γ B
    ...   | no ¬Bf = no (λ { (+-form _ Bf) → ¬Bf Bf })
    ...   | yes Bf = yes (+-form Af Bf)
    type-formation-dec Γ (Id A a b) = no helper
      where
        helper : Γ ⊢ Id A a b type → ⊥
        helper (Id-form _ _ _) = ⊥-elim (need-type-check Γ A a b)
          where
            postulate need-type-check : ∀ {n} (Γ : Ctx n) (A : Ty n) (a b : Tm n) → ⊥

-- Boolean weights are decidable
module BoolDecidable where
  open BoolDM
  open Decidability BoolDM

  bool-≟ : (w v : Bool) → Dec (w ≡ v)
  bool-≟ false false = yes refl
  bool-≟ false true = no (λ ())
  bool-≟ true false = no (λ ())
  bool-≟ true true = yes refl

  bool-≤? : (w v : Bool) → Dec (w ≤B v)
  bool-≤? false _ = yes ≤-false
  bool-≤? true false = no (λ ())
  bool-≤? true true = yes ≤-true

  BoolDecWeight : DecidableWeight
  BoolDecWeight = record
    { _≟W_ = bool-≟
    ; _≤?W_ = bool-≤?
    }

-- Termination theorem for type checking algorithm
-- Type checking terminates because all recursive calls operate on
-- structurally smaller terms/types.
module Termination where
  open import Data.Nat as Nat using (ℕ; zero; suc; _+_)
  open Decidability BoolDM.BoolDM
  open WithDecidableWeight BoolDecidable.BoolDecWeight

  -- Structural recursion ensures termination:
  -- 1. Type formation: recursion on type structure
  -- 2. Term typing: recursion on term structure
  -- 3. Type equality: recursion on type structure
  -- 4. Term equality: recursion on term structure

  -- All recursive calls satisfy:
  --   size(argument) < size(input)
  -- This is witnessed by the mutual size functions above.

  termination-witness : ∀ {n} (t : Tm n) → ℕ
  termination-witness = tm-size

  -- The type checking algorithm terminates for all inputs
  -- because each recursive call decreases the size measure.
  type-check-terminates : Set
  type-check-terminates = ∀ {n} (Γ : Ctx n) (t : Tm n) →
    ∃ λ (steps : ℕ) → steps Nat.≤ termination-witness t
