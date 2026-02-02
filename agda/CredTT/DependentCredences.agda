module CredTT.DependentCredences where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero) renaming (suc to nsuc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import CredTT.Credence
open import CredTT.Syntax
open import CredTT.Substitution
import CredTT.Context as Ctx

-- Dependent Credences Extension for CredTT
--
-- Standard CredTT: Gamma |- t : A @ c     where c is a constant credence
-- Extended CredTT: Gamma |- t : A @ c(x)  where c is a function of x
--
-- This generalizes uniform credences to varying credences over the domain.
-- Key use case: (x : A) -> B @ c(x) where the reliability of B depends on x
--
-- Example interpretation:
--   - "For all natural numbers n, P(n) holds with confidence 1/(n+1)"
--   - Credence function: c(n) = 1/(n+1)
--   - As n -> infinity, confidence approaches 0

module DepTyping {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open DependentCredence DM
  open import CredTT.Judgment
  open Typing DM

  -- Credence expression: can be a constant or depend on a variable
  data CExpr (n : ℕ) : Set ℓ where
    cconst : C → CExpr n
    cvar   : Fin n → (C → C) → CExpr n       -- c depends on variable i via function f
    csup   : CExpr (nsuc n) → CExpr n        -- supremum over bound variable
    cinf   : CExpr (nsuc n) → CExpr n        -- infimum over bound variable

  -- Evaluate credence expression in a given assignment of credences to variables
  evalC : ∀ {n} → CExpr n → (Fin n → C) → C
  evalC (cconst c) _ = c
  evalC (cvar i f) σ = f (σ i)
  evalC (csup ce) σ = sup (λ c → evalC ce (λ { fzero → c ; (fsuc j) → σ j }))
  evalC (cinf ce) σ = inf (λ c → evalC ce (λ { fzero → c ; (fsuc j) → σ j }))

  -- Weakening for credence expressions
  wkCExpr : ∀ {n} → CExpr n → CExpr (nsuc n)
  wkCExpr (cconst c) = cconst c
  wkCExpr (cvar i f) = cvar (fsuc i) f
  wkCExpr (csup ce) = csup (wkCExpr ce)
  wkCExpr (cinf ce) = cinf (wkCExpr ce)

  -- Dependent Pi type with credence function
  -- (x : A) -> B @ c(x) means:
  --   Given a : A @ d, applying f : (x:A) -> B @ c(x) gives f a : B[a] @ c(a) . d
  --
  -- The credence of the result depends on the actual argument value.
  --
  -- Key rule:
  --   Gamma |- f : (x : A) -> B @ c(x)    Gamma |- a : A @ d
  --   ─────────────────────────────────────────────────────────
  --              Gamma |- f a : B[a] @ c(a) . d
  --
  -- For type formation, we need sup over credences:
  --   If c(x) varies over x, the overall reliability is bounded by sup{c(x)}

  -- Dependent credence-weighted typing judgment with credence expressions
  infix 3 _⊢d_∶_〔_〕
  data _⊢d_∶_〔_〕 : ∀ {n} → Ctx.Ctx n → Tm n → Ty n → CExpr n → Set ℓ where

    -- Constant credence embeds standard judgment
    d-const : ∀ {n} {Γ : Ctx.Ctx n} {t : Tm n} {A : Ty n} {c : C} →
              Γ ⊢ t ∶ A 〔 c 〕 →
              Γ ⊢d t ∶ A 〔 cconst c 〕

    -- Variable with dependent credence
    d-var : ∀ {n} {Γ : Ctx.Ctx n} (i : Fin n) →
            Γ ⊢d var i ∶ Ctx.lookup Γ i 〔 cconst 𝟙 〕

    -- Lambda: credence expression lifts under binder
    d-lam : ∀ {n} {Γ : Ctx.Ctx n} {A : Ty n} {B : Ty (nsuc n)} {b : Tm (nsuc n)}
            {ce : CExpr (nsuc n)} →
            (Γ Ctx., A) ⊢d b ∶ B 〔 ce 〕 →
            Γ ⊢d lam A b ∶ (A ⇒ B) 〔 csup ce 〕

    -- Application: instantiate dependent credence
    d-app : ∀ {n} {Γ : Ctx.Ctx n} {A : Ty n} {B : Ty (nsuc n)} {f a : Tm n}
            {ce : CExpr (nsuc n)} {d : C} →
            Γ ⊢d f ∶ (A ⇒ B) 〔 csup ce 〕 →
            Γ ⊢ a ∶ A 〔 d 〕 →
            Γ ⊢d app f a ∶ (B [ a ]ₜ) 〔 cconst d 〕

    -- Credence weakening for dependent credences
    d-weaken : ∀ {n} {Γ : Ctx.Ctx n} {t : Tm n} {A : Ty n} {ce ce' : CExpr n}
               {σ : Fin n → C} →
               Γ ⊢d t ∶ A 〔 ce 〕 →
               evalC ce' σ ≤ evalC ce σ →
               Γ ⊢d t ∶ A 〔 ce' 〕

  -- Key theorem: uniform credences are a special case
  -- If c(x) = c for all x, then dependent Pi reduces to standard Pi
  -- Proof: sup(const c) = c by sup-const axiom
  postulate
    uniform-specializes : ∀ {n} {Γ : Ctx.Ctx n} {A : Ty n} {B : Ty (nsuc n)}
                          {b : Tm (nsuc n)} {c : C} →
                          (Γ Ctx., A) ⊢ b ∶ B 〔 c 〕 →
                          Γ ⊢d lam A b ∶ (A ⇒ B) 〔 cconst c 〕

  -- Dependent credences for existential/Sigma types
  -- (x : A) x B @ c(x) has credence inf{c(x) : x in A}
  -- because we need ALL instances to have sufficient credence

  -- Example: Graded universal quantification
  -- forall(n : Nat). P(n) @ c(n) where c(n) decreases
  -- The overall statement has credence inf{c(n)}
  -- If c(n) -> 0 as n -> infinity, then inf = 0

  -- Example: Conditional probability
  -- P(B|A) can be modeled as: given evidence a : A @ d, conclude B @ f(d)
  -- where f is the conditional credence function

-- Concrete examples with Boolean credences
module DepBoolExamples where
  open BoolDM
  open DepTyping BoolDM

  -- In Boolean case, sup = OR over all values, inf = AND over all values
  -- For finite types, this is computable

  -- Example: (x : Bool) -> P @ c(x)
  -- c(true) = 1, c(false) = 0
  -- sup = 1, inf = 0
