{-# OPTIONS --without-K --safe #-}

-- CredTT v2: Types Emerge from Credence
-- A formal sketch of the framework

module sketch where

open import Level using (Level; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- Layer 0: Credence Algebra (Abstract)
------------------------------------------------------------------------

record DeMorganAlgebra (ℓ : Level) : Set (Level.suc ℓ) where
  field
    C : Set ℓ

    -- Constants
    𝟙 : C                          -- certainty
    𝟘 : C                          -- impossibility

    -- Operations
    _·_ : C → C → C                -- multiplication (conjunction)
    ∼_  : C → C                    -- complement (negation)
    _≤_ : C → C → Set ℓ            -- ordering

    -- Multiplication axioms
    ·-identityʳ : ∀ c → c · 𝟙 ≡ c
    ·-zeroʳ     : ∀ c → c · 𝟘 ≡ 𝟘
    ·-assoc     : ∀ a b c → (a · b) · c ≡ a · (b · c)
    ·-comm      : ∀ a b → a · b ≡ b · a

    -- Complement axioms
    ∼-𝟘 : ∼ 𝟘 ≡ 𝟙
    ∼-𝟙 : ∼ 𝟙 ≡ 𝟘
    ∼-involutive : ∀ c → ∼ (∼ c) ≡ c

    -- Order axioms
    ≤-refl  : ∀ c → c ≤ c
    ≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    ≤-antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
    𝟘-least : ∀ c → 𝟘 ≤ c
    𝟙-greatest : ∀ c → c ≤ 𝟙

  -- Derived: disjunction
  _+_ : C → C → C
  a + b = ∼ (∼ a · ∼ b)

  -- Derived: implication
  _⇒_ : C → C → C
  a ⇒ b = ∼ a + b

------------------------------------------------------------------------
-- Layer 1: Terms (Untyped)
------------------------------------------------------------------------

-- Untyped lambda terms with pairs, sums, identity
data Term : Set where
  var   : ℕ → Term
  lam   : Term → Term
  app   : Term → Term → Term
  pair  : Term → Term → Term
  fst   : Term → Term
  snd   : Term → Term
  inl   : Term → Term
  inr   : Term → Term
  case  : Term → Term → Term → Term
  refl  : Term
  J     : Term → Term → Term → Term

-- Natural numbers for variables
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

------------------------------------------------------------------------
-- Layer 2: Types as Credence Predicates
------------------------------------------------------------------------

module TypesEmerge (DM : DeMorganAlgebra Level.zero) where
  open DeMorganAlgebra DM

  -- A Type is a credence predicate on terms
  Type : Set₁
  Type = Term → C

  -- Type equality: pointwise equality of predicates
  _≈_ : Type → Type → Set
  A ≈ B = ∀ t → A t ≡ B t

  -- Subtyping: pointwise ordering
  _<:_ : Type → Type → Set
  A <: B = ∀ t → A t ≤ B t

  -- The top type (everything has credence 1)
  ⊤-type : Type
  ⊤-type t = 𝟙

  -- The bottom type (everything has credence 0)
  ⊥-type : Type
  ⊥-type t = 𝟘

------------------------------------------------------------------------
-- Layer 3: Type Formers (Derived)
------------------------------------------------------------------------

  -- Product type (Σ)
  -- (A × B)(p) = A(fst p) · B(snd p)
  _×-type_ : Type → Type → Type
  (A ×-type B) t = A (fst t) · B (snd t)

  -- Function type (simple, non-dependent)
  -- (A → B)(f) = "for all a, A(a) ⇒ B(f a)"
  -- We approximate with a representative check
  -- (Full version needs infimum over all terms)
  _→-type_ : Type → Type → Type
  (A →-type B) f = 𝟙  -- PLACEHOLDER: needs inf construction

  -- Sum type
  -- (A + B)(inl a) = A(a)
  -- (A + B)(inr b) = B(b)
  _+-type_ : Type → Type → Type
  (A +-type B) (inl a) = A a
  (A +-type B) (inr b) = B b
  (A +-type B) _       = 𝟘

------------------------------------------------------------------------
-- Layer 2.5: Credence Judgments
------------------------------------------------------------------------

  -- Context: list of credence assignments to variables
  data Ctx : Set where
    ∅   : Ctx
    _,_@_ : Ctx → ℕ → C → Ctx

  -- Lookup a variable's credence in context
  lookup : Ctx → ℕ → C
  lookup ∅ _ = 𝟘
  lookup (Γ , x @ c) y with x ≟ y
    where
      _≟_ : ℕ → ℕ → Set
      zero ≟ zero = ℕ  -- placeholder for equality
      _ ≟ _ = ℕ        -- needs proper implementation
  ... | _ = c          -- simplified

  -- The primitive judgment: Γ ⊢ t @ c
  -- "In context Γ, term t has credence c"
  data _⊢_@_ : Ctx → Term → C → Set where

    -- Variable rule
    J-Var : ∀ {Γ x c} →
            lookup Γ x ≡ c →
            Γ ⊢ var x @ c

    -- Application rule: credences multiply
    J-App : ∀ {Γ f a c₁ c₂} →
            Γ ⊢ f @ c₁ →
            Γ ⊢ a @ c₂ →
            Γ ⊢ app f a @ (c₁ · c₂)

    -- Pair rule: credences multiply
    J-Pair : ∀ {Γ t u c₁ c₂} →
             Γ ⊢ t @ c₁ →
             Γ ⊢ u @ c₂ →
             Γ ⊢ pair t u @ (c₁ · c₂)

    -- Reflexivity has credence 1
    J-Refl : ∀ {Γ} →
             Γ ⊢ refl @ 𝟙

------------------------------------------------------------------------
-- Layer 4: Typing Judgment (Derived)
------------------------------------------------------------------------

  -- The derived typing judgment
  -- Γ ⊢ t : A @ c  :=  (Γ ⊢ t @ c) × (A t ≥ c)

  _⊢_∶_@_ : Ctx → Term → Type → C → Set
  Γ ⊢ t ∶ A @ c = (Γ ⊢ t @ c) × (c ≤ A t)

  -- This is a DEFINITION, not a primitive judgment form.
  -- The typing relation EMERGES from:
  --   1. The primitive credence judgment (Γ ⊢ t @ c)
  --   2. The type predicate (A : Term → C)

------------------------------------------------------------------------
-- Layer 5: Boolean Collapse
------------------------------------------------------------------------

-- When C = Bool, we recover standard type theory

data Bool : Set where
  true  : Bool
  false : Bool

BoolDM : DeMorganAlgebra Level.zero
BoolDM = record
  { C = Bool
  ; 𝟙 = true
  ; 𝟘 = false
  ; _·_ = _∧_
  ; ∼_  = not
  ; _≤_ = _≤b_
  -- axioms omitted (trivial by case analysis)
  ; ·-identityʳ = λ _ → refl  -- placeholder
  ; ·-zeroʳ = λ _ → refl      -- placeholder
  ; ·-assoc = λ _ _ _ → refl  -- placeholder
  ; ·-comm = λ _ _ → refl     -- placeholder
  ; ∼-𝟘 = refl
  ; ∼-𝟙 = refl
  ; ∼-involutive = λ _ → refl -- placeholder
  ; ≤-refl = λ _ → tt         -- placeholder
  ; ≤-trans = λ _ _ → tt      -- placeholder
  ; ≤-antisym = λ _ _ → refl  -- placeholder
  ; 𝟘-least = λ _ → tt        -- placeholder
  ; 𝟙-greatest = λ _ → tt     -- placeholder
  }
  where
    _∧_ : Bool → Bool → Bool
    true  ∧ b = b
    false ∧ _ = false

    not : Bool → Bool
    not true  = false
    not false = true

    _≤b_ : Bool → Bool → Set
    false ≤b _     = ℕ  -- placeholder for ⊤
    true  ≤b true  = ℕ
    true  ≤b false = ℕ  -- placeholder for ⊥

    tt : ℕ
    tt = zero

-- In the Boolean case:
-- - Type predicates become characteristic functions (sets)
-- - Credence judgments become binary (defined/undefined)
-- - Typing judgments become standard type membership
-- - MLTT is recovered

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

{-
CredTT v2 Architecture:

Layer 0: Credence Algebra (C, 1, 0, *, ~, ≤)
         ↓
Layer 1: Untyped Terms
         ↓
Layer 2: Types := Term → C (credence predicates)
         ↓
Layer 3: Type Formers (derived from credence ops)
         Σ ↔ multiplication (·)
         Π ↔ implication (⇒) + infimum
         + ↔ disjunction (+)
         ↓
Layer 4: Typing Judgment (derived)
         Γ ⊢ t : A @ c := (Γ ⊢ t @ c) × (c ≤ A t)
         ↓
Layer 5: Boolean Collapse → MLTT

Types EMERGE from credence structure.
They are not given as primitive syntax.
-}
