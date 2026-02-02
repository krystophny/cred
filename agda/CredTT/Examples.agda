module CredTT.Examples where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CredTT.Credence
open import CredTT.Syntax
open import CredTT.Substitution
open import CredTT.Context
open import CredTT.Judgment

-- Examples using Boolean credences (the MLTT case)
module BoolExamples where
  open BoolDM
  open Typing BoolDM

  -- A base type for examples
  Nat : ∀ {n} → Ty n
  Nat = base 0

  -- Identity function: lam x.x : A -> A @ 1
  -- The identity always has credence 1
  id-term : ∀ {n} → Tm n
  id-term = lam Nat (var zero)

  id-typed : ∀ {n} {Γ : Ctx n} → Γ ⊢ id-term ∶ (Nat ⇒ wkTy Nat) 〔 true 〕
  id-typed = t-lam (t-var zero)

  -- Application of identity: id a : A [ c ] when a : A [ c ]
  -- Credence is preserved through identity
  id-app : ∀ {n} {Γ : Ctx n} {a : Tm n} {c : Bool} →
           Γ ⊢ a ∶ Nat 〔 c 〕 →
           Γ ⊢ app id-term a ∶ Nat 〔 c 〕
  id-app {c = c} d = subst-eq (t-app id-typed d) (∧-identityˡ c)
    where
      subst-eq : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c c' : Bool} →
                 Γ ⊢ t ∶ A 〔 c 〕 →
                 c ≡ c' →
                 Γ ⊢ t ∶ A 〔 c' 〕
      subst-eq d refl = d

  -- Pair: (a, b) : A x B [ c.d ]
  -- The joint credence is the product
  pair-example : ∀ {n} {Γ : Ctx n} {a b : Tm n} {c d : Bool} →
                 Γ ⊢ a ∶ Nat 〔 c 〕 →
                 Γ ⊢ b ∶ Nat 〔 d 〕 →
                 Γ ⊢ pair a b ∶ (Nat ×' wkTy Nat) 〔 c ∧B d 〕
  pair-example da db = t-pair da db

  -- Credence multiplication: at credence true, composition works normally
  -- f : A -> B @ 1, g : B -> C @ 1 |- g o f : A -> C @ 1
  compose-term : ∀ {n} → Tm (suc (suc n))
  compose-term = lam Nat (app (var (suc zero)) (app (var (suc (suc zero))) (var zero)))

  -- At credence false (= 0), everything is trivially satisfied
  -- This is because false . d = false for any d
  credence-zero-trivial : ∀ (d : Bool) → false ∧B d ≡ false
  credence-zero-trivial d = refl

  -- Sum case: demonstrate credence multiplication in elimination
  -- case e of inl x -> l | inr y -> r : D [ c.d ]
  sum-elim-example : ∀ {n} {Γ : Ctx n} {e : Tm n} {c d : Bool} →
                     Γ ⊢ e ∶ (Nat +' Nat) 〔 c 〕 →
                     (Γ , Nat) ⊢ var zero ∶ wkTy Nat 〔 d 〕 →
                     (Γ , Nat) ⊢ var zero ∶ wkTy Nat 〔 d 〕 →
                     Γ ⊢ case e (var zero) (var zero) ∶ Nat 〔 c ∧B d 〕
  sum-elim-example = t-case

  -- ===================================================================
  -- PURE CredTT: No Unit Type, No Empty Type
  -- ===================================================================
  --
  -- In pure CredTT:
  -- - There is no Unit type (One'). Certainty is credence 1 on ANY type.
  -- - There is no Empty type (Zero'). Impossibility is credence 0 on ANY type.
  --
  -- This avoids the philosophical question "what TYPE is credence 0/1?"
  --
  -- GRADED EX FALSO:
  -- If a : A @ 0, then f a : B [ c.0 ] = 0 automatically.
  -- Credence 0 propagates through all operations. No explosion, no abort.
  --
  -- PROOF BY CONTRADICTION (at meta-level):
  -- We can prove in Agda (the meta-language) that certain credences must be 0.
  -- This is sound because we're reasoning ABOUT credences, not deriving terms.
  -- ===================================================================

-- Key insight: In Boolean algebra, true . true = true
-- This means at credence 1, composition preserves full certainty.
-- But at any lower credence, multiplication reduces certainty.

-- Example: If P(A) = 0.9 and P(B|A) = 0.9, then P(A,B) = 0.81
-- In Boolean: true . true = true (full certainty preserved)
-- In [0,1]: 0.9 . 0.9 = 0.81 (certainty reduces)
