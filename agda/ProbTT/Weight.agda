module ProbTT.Weight where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)

-- De Morgan Algebra: multiplication, complement, order
-- No addition! Disjunction derived via De Morgan duality.
record DeMorganAlgebra (ℓ : Level) : Set (suc ℓ) where
  field
    W : Set ℓ
    𝟘 : W
    𝟙 : W
    _·_ : W → W → W
    ¬_ : W → W
    _≤_ : W → W → Set ℓ

    -- Multiplication axioms (6)
    ·-identityʳ : ∀ w → w · 𝟙 ≡ w
    ·-identityˡ : ∀ w → 𝟙 · w ≡ w
    ·-annihilʳ  : ∀ w → w · 𝟘 ≡ 𝟘
    ·-annihilˡ  : ∀ w → 𝟘 · w ≡ 𝟘
    ·-assoc     : ∀ u v w → (u · v) · w ≡ u · (v · w)
    ·-comm      : ∀ u v → u · v ≡ v · u

    -- Complement axioms (3)
    ¬-𝟘    : ¬ 𝟘 ≡ 𝟙
    ¬-𝟙    : ¬ 𝟙 ≡ 𝟘
    ¬-invol : ∀ w → ¬ (¬ w) ≡ w

    -- Order axioms (5)
    ≤-refl     : ∀ w → w ≤ w
    ≤-trans    : ∀ {u v w} → u ≤ v → v ≤ w → u ≤ w
    ≤-antisym  : ∀ {u v} → u ≤ v → v ≤ u → u ≡ v
    𝟘-least    : ∀ w → 𝟘 ≤ w
    𝟙-greatest : ∀ w → w ≤ 𝟙

  -- Derived: De Morgan disjunction
  -- w ∨ v = ¬(¬w · ¬v)
  -- In [0,1]: w ∨ v = 1 - (1-w)(1-v) = w + v - wv
  _∨_ : W → W → W
  w ∨ v = ¬ (¬ w · ¬ v)

  infixl 7 _·_
  infixl 6 _∨_
  infix  4 _≤_

-- Boolean De Morgan algebra: the {0,1} case
-- This is what gives us MLTT when used as weights
module BoolDM where

  -- Order on Bool: a ≤ b iff a = false or b = true
  data _≤B_ : Bool → Bool → Set where
    ≤-false : ∀ {b} → false ≤B b
    ≤-true  : ∀ {a} → a ≤B true

  -- Boolean AND
  _∧B_ : Bool → Bool → Bool
  _∧B_ = _∧_

  -- Boolean NOT
  notB : Bool → Bool
  notB = not

  -- Proofs of multiplication axioms
  ∧-identityʳ : ∀ w → w ∧B true ≡ w
  ∧-identityʳ false = refl
  ∧-identityʳ true  = refl

  ∧-identityˡ : ∀ w → true ∧B w ≡ w
  ∧-identityˡ w = refl

  ∧-annihilʳ : ∀ w → w ∧B false ≡ false
  ∧-annihilʳ false = refl
  ∧-annihilʳ true  = refl

  ∧-annihilˡ : ∀ w → false ∧B w ≡ false
  ∧-annihilˡ w = refl

  ∧-assoc : ∀ u v w → (u ∧B v) ∧B w ≡ u ∧B (v ∧B w)
  ∧-assoc false v w = refl
  ∧-assoc true  v w = refl

  ∧-comm : ∀ u v → u ∧B v ≡ v ∧B u
  ∧-comm false false = refl
  ∧-comm false true  = refl
  ∧-comm true  false = refl
  ∧-comm true  true  = refl

  -- Proofs of complement axioms
  not-false : notB false ≡ true
  not-false = refl

  not-true : notB true ≡ false
  not-true = refl

  not-invol : ∀ w → notB (notB w) ≡ w
  not-invol false = refl
  not-invol true  = refl

  -- Proofs of order axioms
  ≤B-refl : ∀ w → w ≤B w
  ≤B-refl false = ≤-false
  ≤B-refl true  = ≤-true

  ≤B-trans : ∀ {u v w} → u ≤B v → v ≤B w → u ≤B w
  ≤B-trans ≤-false _       = ≤-false
  ≤B-trans ≤-true  ≤-true  = ≤-true

  ≤B-antisym : ∀ {u v} → u ≤B v → v ≤B u → u ≡ v
  ≤B-antisym ≤-false ≤-false = refl
  ≤B-antisym ≤-true  ≤-true  = refl

  false-least : ∀ w → false ≤B w
  false-least w = ≤-false

  true-greatest : ∀ w → w ≤B true
  true-greatest w = ≤-true

  -- The complete Boolean De Morgan algebra
  BoolDM : DeMorganAlgebra _
  BoolDM = record
    { W           = Bool
    ; 𝟘           = false
    ; 𝟙           = true
    ; _·_         = _∧B_
    ; ¬_          = notB
    ; _≤_         = _≤B_
    ; ·-identityʳ = ∧-identityʳ
    ; ·-identityˡ = ∧-identityˡ
    ; ·-annihilʳ  = ∧-annihilʳ
    ; ·-annihilˡ  = ∧-annihilˡ
    ; ·-assoc     = ∧-assoc
    ; ·-comm      = ∧-comm
    ; ¬-𝟘         = not-false
    ; ¬-𝟙         = not-true
    ; ¬-invol     = not-invol
    ; ≤-refl      = ≤B-refl
    ; ≤-trans     = ≤B-trans
    ; ≤-antisym   = ≤B-antisym
    ; 𝟘-least     = false-least
    ; 𝟙-greatest  = true-greatest
    }

open BoolDM public using (BoolDM)

-- De Morgan laws (derived)
module DeMorganLaws {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  private
    cong₂ : ∀ {A B C : Set ℓ} (f : A → B → C) {x y u v : A} →
            x ≡ y → u ≡ v → f x u ≡ f y v
    cong₂ f refl refl = refl

  -- ¬(w · v) = ¬w ∨ ¬v
  -- By definition: ¬w ∨ ¬v = ¬(¬¬w · ¬¬v) = ¬(w · v)
  demorgan-· : ∀ w v → ¬ (w · v) ≡ (¬ w) ∨ (¬ v)
  demorgan-· w v = cong ¬_ (sym (cong₂ _·_ (¬-invol w) (¬-invol v)))

  -- ¬(w ∨ v) = ¬w · ¬v
  -- ¬(w ∨ v) = ¬¬(¬w · ¬v) = ¬w · ¬v
  demorgan-∨ : ∀ w v → ¬ (w ∨ v) ≡ (¬ w) · (¬ v)
  demorgan-∨ w v = ¬-invol (¬ w · ¬ v)
