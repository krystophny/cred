module ProbTT.Properties where

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Substitution
open import ProbTT.Context
open import ProbTT.Judgment

-- Properties of the typing system
module Props {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM

  -- Weight bound: all weights are bounded by 𝟙
  -- This follows from: we can only lower weights, and variables are at 𝟙
  weight-bounded : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w : W} →
                   Γ ⊢ t ∶ A @ w →
                   w ≤ 𝟙
  weight-bounded (t-var i)         = ≤-refl 𝟙
  weight-bounded (t-weaken d v≤w)  = ≤-trans v≤w (weight-bounded d)
  weight-bounded (t-lam d)         = weight-bounded d
  weight-bounded (t-app df da)     = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  weight-bounded (t-pair da db)    = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  weight-bounded (t-fst d)         = weight-bounded d
  weight-bounded (t-snd d)         = weight-bounded d
  weight-bounded (t-inl d)         = weight-bounded d
  weight-bounded (t-inr d)         = weight-bounded d
  weight-bounded (t-case de dl dr) = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)
  weight-bounded t-star            = ≤-refl 𝟙
  weight-bounded (t-abort d)       = weight-bounded d
  weight-bounded (t-refl d)        = weight-bounded d
  weight-bounded (t-J dp dd)       = 𝟙-greatest (DeMorganAlgebra._·_ DM _ _)

  -- Weight monotonicity: multiplication preserves order
  -- If v ≤ w then u · v ≤ u · w
  -- This requires additional axioms on the algebra (monotonicity of ·)
  -- For now we leave this as a postulate since it holds in all standard instances

  -- Weakening is admissible (structural rule)
  -- If Γ ⊢ t : A @ w then Γ,B ⊢ wk t : wk A @ w
  -- This follows by induction on the derivation

  -- Substitution is admissible (key structural lemma)
  -- If Γ ⊢ a : A @ w and Γ,A ⊢ b : B @ v then Γ ⊢ b[a] : B[a] @ w·v

  -- Identity at weight 𝟙
  id-typed : ∀ {n} {Γ : Ctx n} {A : Ty n} →
             Γ ⊢ A type →
             Γ ⊢ lam A (var zero) ∶ (A ⇒ wkTy A) @ 𝟙
  id-typed Af = t-lam (t-var zero)

  -- Composition multiplies weights
  -- Given f : A → B @ w and g : B → C @ v
  -- We get g ∘ f : A → C @ w · v

  -- Graded ex falso: from ⊥ at weight w, anything at weight w
  graded-ex-falso : ∀ {n} {Γ : Ctx n} {A : Ty n} {e : Tm n} {w : W} →
                    Γ ⊢ e ∶ 𝟘' @ w →
                    Γ ⊢ abort A e ∶ A @ w
  graded-ex-falso = t-abort

  -- At weight 𝟘, the ex falso is unconstrained
  -- w = 𝟘 means the antecedent is impossible, so anything follows
  -- This is the continuous generalization of classical ex falso

  -- Multiplication annihilates at 𝟘
  zero-annihilates : ∀ (w : W) → w · 𝟘 ≡ 𝟘
  zero-annihilates = ·-annihilʳ

  -- Type preservation under beta reduction
  -- If Γ ⊢ t ≡ t' : A @ w then Γ ⊢ t : A @ w and Γ ⊢ t' : A @ w
  preservation-left : ∀ {n} {Γ : Ctx n} {t t' : Tm n} {A : Ty n} {w : W} →
                      Γ ⊢ t ≡ t' ∶ A @ w →
                      Γ ⊢ t ∶ A @ w
  preservation-left (eq-refl d) = d
  preservation-left (eq-sym eq) = preservation-right eq
    where
      preservation-right : ∀ {n} {Γ : Ctx n} {t t' : Tm n} {A : Ty n} {w : W} →
                           Γ ⊢ t ≡ t' ∶ A @ w →
                           Γ ⊢ t' ∶ A @ w
      preservation-right (eq-refl d) = d
      preservation-right (eq-sym eq) = preservation-left eq
      preservation-right (eq-trans eq1 eq2) = preservation-right eq2
      preservation-right (Π-β db da) = subst-typed db da
        where
          subst-typed : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)}
                          {b : Tm (suc n)} {a : Tm n} {w v : W} →
                        (Γ , A) ⊢ b ∶ B @ w →
                        Γ ⊢ a ∶ A @ v →
                        Γ ⊢ (b [ a ]) ∶ (B [ a ]ₜ) @ (w · v)
          subst-typed db da = {!admissible!}  -- substitution lemma
      preservation-right (Σ-β₁ da db) = da
      preservation-right (Σ-β₂ da db) = db
      preservation-right (+-β-inl da dl dr) = {!admissible!}  -- substitution
      preservation-right (+-β-inr db dl dr) = {!admissible!}  -- substitution
      preservation-right (Id-β da dd) = dd
  preservation-left (eq-trans eq1 eq2) = preservation-left eq1
  preservation-left (Π-β db da) = t-app (t-lam db) da
  preservation-left (Σ-β₁ da db) = t-fst (t-pair da db)
  preservation-left (Σ-β₂ da db) = t-snd (t-pair da db)
  preservation-left (+-β-inl da dl dr) = t-case (t-inl da) dl dr
  preservation-left (+-β-inr db dl dr) = t-case (t-inr db) dl dr
  preservation-left (Id-β da dd) = t-J (t-refl da) dd
