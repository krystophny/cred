# Agda Formalization Plan for ProbTT

## Goal

Formalize ProbTT as an **object language** in Agda, proving:
1. The type system is well-defined
2. MLTT is the {0,1} limiting case
3. Conditioning via chain rule is sound

## File Structure

```
agda/
  ProbTT/
    Weight.agda           -- De Morgan algebra
    Syntax.agda           -- Terms and types
    Context.agda          -- Contexts
    Judgment.agda         -- Weighted judgments
    Rules.agda            -- Typing rules
    Properties.agda       -- Metatheorems
    MLTT.agda             -- Classical limit
    Examples.agda         -- Worked examples
  Everything.agda         -- Module exports
  probtt.agda-lib         -- Library file
```

## Phase 1: Weight Algebra

### Weight.agda

```agda
module ProbTT.Weight where

open import Level
open import Relation.Binary.PropositionalEquality

-- Abstract De Morgan algebra
record DeMorganAlgebra (ℓ : Level) : Set (suc ℓ) where
  field
    W : Set ℓ
    𝟘 : W
    𝟙 : W
    _·_ : W → W → W
    ¬_ : W → W
    _≤_ : W → W → Set ℓ

    -- Multiplication axioms
    ·-identityʳ : ∀ w → w · 𝟙 ≡ w
    ·-identityˡ : ∀ w → 𝟙 · w ≡ w
    ·-annihilʳ : ∀ w → w · 𝟘 ≡ 𝟘
    ·-annihilˡ : ∀ w → 𝟘 · w ≡ 𝟘
    ·-assoc : ∀ u v w → (u · v) · w ≡ u · (v · w)
    ·-comm : ∀ u v → u · v ≡ v · u

    -- Complement axioms
    ¬-𝟘 : ¬ 𝟘 ≡ 𝟙
    ¬-𝟙 : ¬ 𝟙 ≡ 𝟘
    ¬-invol : ∀ w → ¬ (¬ w) ≡ w

    -- Order axioms
    ≤-refl : ∀ w → w ≤ w
    ≤-trans : ∀ {u v w} → u ≤ v → v ≤ w → u ≤ w
    ≤-antisym : ∀ {u v} → u ≤ v → v ≤ u → u ≡ v
    𝟘-least : ∀ w → 𝟘 ≤ w
    𝟙-greatest : ∀ w → w ≤ 𝟙

  -- Derived: De Morgan disjunction
  _∨_ : W → W → W
  w ∨ v = ¬ (¬ w · ¬ v)
```

### Instances

```agda
-- Boolean instance (for MLTT)
BoolDM : DeMorganAlgebra lzero
BoolDM = record
  { W = Bool
  ; 𝟘 = false
  ; 𝟙 = true
  ; _·_ = _∧_
  ; ¬_ = not
  ; _≤_ = λ a b → a ≡ false ⊎ b ≡ true
  ; ... -- proofs
  }

-- Unit interval instance (for probability)
-- (Would need postulates or use of rationals)
```

## Phase 2: Syntax

### Syntax.agda

```agda
module ProbTT.Syntax where

open import Data.Nat using (ℕ)
open import ProbTT.Weight

-- Raw terms (untyped)
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
  star  : Term
  abort : Term → Term
  refl  : Term

-- Raw types
data Type : Set where
  base  : ℕ → Type                    -- Base types
  _⇒_   : Type → Type → Type          -- Function
  _×'_  : Type → Type → Type          -- Product
  _+'_  : Type → Type → Type          -- Sum
  𝟙'    : Type                        -- Unit
  𝟘'    : Type                        -- Empty
  Id    : Type → Term → Term → Type   -- Identity
```

## Phase 3: Judgments and Rules

### Judgment.agda

```agda
module ProbTT.Judgment (DM : DeMorganAlgebra lzero) where

open DeMorganAlgebra DM
open import ProbTT.Syntax

-- Typing context
data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Type → Ctx

-- Weighted typing judgment: Γ ⊢ t : A @ w
data _⊢_∶_@_ : Ctx → Term → Type → W → Set where

  -- Variables have weight 𝟙
  t-var : ∀ {Γ A} →
          (Γ , A) ⊢ var 0 ∶ A @ 𝟙

  -- Weakening with weight preservation
  t-weak : ∀ {Γ A B t w} →
           Γ ⊢ t ∶ A @ w →
           (Γ , B) ⊢ wk t ∶ A @ w

  -- Function introduction
  t-lam : ∀ {Γ A B t w} →
          (Γ , A) ⊢ t ∶ B @ w →
          Γ ⊢ lam t ∶ (A ⇒ B) @ w

  -- Function elimination (weights multiply)
  t-app : ∀ {Γ A B f a w v} →
          Γ ⊢ f ∶ (A ⇒ B) @ w →
          Γ ⊢ a ∶ A @ v →
          Γ ⊢ app f a ∶ B @ (w · v)

  -- Pair introduction (weights multiply)
  t-pair : ∀ {Γ A B a b w v} →
           Γ ⊢ a ∶ A @ w →
           Γ ⊢ b ∶ B @ v →
           Γ ⊢ pair a b ∶ (A ×' B) @ (w · v)

  -- Projections preserve weight
  t-fst : ∀ {Γ A B t w} →
          Γ ⊢ t ∶ (A ×' B) @ w →
          Γ ⊢ fst t ∶ A @ w

  t-snd : ∀ {Γ A B t w} →
          Γ ⊢ t ∶ (A ×' B) @ w →
          Γ ⊢ snd t ∶ B @ w

  -- Sum introduction
  t-inl : ∀ {Γ A B a w} →
          Γ ⊢ a ∶ A @ w →
          Γ ⊢ inl a ∶ (A +' B) @ w

  t-inr : ∀ {Γ A B b w} →
          Γ ⊢ b ∶ B @ w →
          Γ ⊢ inr b ∶ (A +' B) @ w

  -- Unit
  t-star : ∀ {Γ} →
           Γ ⊢ star ∶ 𝟙' @ 𝟙

  -- Empty elimination (ex falso)
  t-abort : ∀ {Γ A e w} →
            Γ ⊢ e ∶ 𝟘' @ w →
            Γ ⊢ abort e ∶ A @ w

  -- Identity
  t-refl : ∀ {Γ A a w} →
           Γ ⊢ a ∶ A @ w →
           Γ ⊢ refl ∶ Id A a a @ w

  -- Weight weakening
  t-weaken-weight : ∀ {Γ t A w v} →
                    Γ ⊢ t ∶ A @ w →
                    v ≤ w →
                    Γ ⊢ t ∶ A @ v
```

## Phase 4: Properties

### Properties.agda

```agda
module ProbTT.Properties (DM : DeMorganAlgebra lzero) where

open import ProbTT.Judgment DM

-- Weight 𝟙 is maximal
max-weight : ∀ {Γ t A w} →
             Γ ⊢ t ∶ A @ w →
             w ≤ 𝟙

-- Composition multiplies weights
weight-compose : ∀ {Γ A B C f g w v} →
                 Γ ⊢ f ∶ (A ⇒ B) @ w →
                 Γ ⊢ g ∶ (B ⇒ C) @ v →
                 Γ ⊢ lam (app (wk g) (app (wk f) (var 0))) ∶ (A ⇒ C) @ (w · v)
```

## Phase 5: MLTT Embedding

### MLTT.agda

```agda
module ProbTT.MLTT where

open import ProbTT.Weight
open import ProbTT.Judgment BoolDM

-- Standard MLTT judgment (weight-free)
data _⊢_∶_ : Ctx → Term → Type → Set where
  ...

-- Embedding: MLTT → ProbTT with weight 𝟙
embed : ∀ {Γ t A} →
        Γ ⊢ t ∶ A →
        Γ ⊢ t ∶ A @ true

-- Collapse: ProbTT with Boolean weights → MLTT
collapse : ∀ {Γ t A} →
           Γ ⊢ t ∶ A @ true →
           Γ ⊢ t ∶ A
```

## Phase 6: Conditioning

### Conditioning.agda

```agda
module ProbTT.Conditioning (DM : DeMorganAlgebra lzero) where

open DeMorganAlgebra DM
open import ProbTT.Judgment DM

-- Chain rule: joint = marginal · conditional
-- P(A,B) = P(A) · P(B|A)

-- Expressed in type theory:
-- If (a,b) : A × B @ w·v
-- Then a : A @ w and b|a : B @ v

-- This is implicit in our pair rule:
-- t-pair gives (a,b) : A × B @ w·v from a : A @ w and b : B @ v

-- The "conditional" interpretation:
-- b has weight v "given" a has weight w
-- The joint (a,b) has weight w·v

-- Graded ex falso:
-- When w = 𝟘, any v satisfies 𝟘 · v = 𝟘
graded-ex-falso : ∀ {Γ A B a b v} →
                  Γ ⊢ a ∶ A @ 𝟘 →
                  Γ ⊢ b ∶ B @ v →
                  Γ ⊢ pair a b ∶ (A ×' B) @ 𝟘
```

## Timeline

| Week | Task |
|------|------|
| 1 | Set up Agda project, Weight.agda |
| 2 | Syntax.agda, Context.agda |
| 3 | Judgment.agda (core rules) |
| 4 | Judgment.agda (remaining rules) |
| 5 | Properties.agda |
| 6 | MLTT.agda (embedding) |
| 7 | MLTT.agda (collapse theorem) |
| 8 | Conditioning.agda, Examples.agda |

## Success Criteria

1. **Agda compiles** without holes or postulates (except for weight algebra axioms)
2. **MLTT embedding** proved: classical logic is the {0,1} case
3. **Weight multiplication** verified: elimination multiplies weights
4. **Graded ex falso** demonstrated: w=0 allows any conditional weight

## Dependencies

- Agda 2.6.4+
- agda-stdlib 2.0+

## Getting Started

```bash
# Install Agda
# On Arch: pacman -S agda agda-stdlib

# Create project
mkdir -p agda/ProbTT
cd agda

# Create library file
echo "name: probtt
include: .
depend: standard-library" > probtt.agda-lib

# Start with Weight.agda
```
