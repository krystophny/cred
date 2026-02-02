{- AXIOM STATUS SUMMARY for Weight.agda (DependentWeight module)

sup, sup-upper, sup-least: COMPLETENESS EXTENSION
  The De Morgan algebra does not include completeness.
  These axioms extend the algebra to a complete lattice.
  For Bool: sup = OR (trivially finite).
  For [0,1]: sup exists by completeness of reals.

inf, inf-lower, inf-greatest: COMPLETENESS EXTENSION
  Same as sup. For Bool: inf = AND.

sup-const, inf-const: SHOULD BE PROVEN
  Given inhabited index type, sup/inf of constant function equals constant.
  Requires index type to be non-empty.
-}
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

    -- Order axioms (6)
    ≤-refl     : ∀ w → w ≤ w
    ≤-trans    : ∀ {u v w} → u ≤ v → v ≤ w → u ≤ w
    ≤-antisym  : ∀ {u v} → u ≤ v → v ≤ u → u ≡ v
    𝟘-least    : ∀ w → 𝟘 ≤ w
    𝟙-greatest : ∀ w → w ≤ 𝟙
    ·-≤-self   : ∀ w v → w · v ≤ w  -- multiplication decreases (w·v ≤ w)

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

  -- Multiplication decreases: w ∧ v ≤ w
  ∧-≤-self : ∀ w v → (w ∧B v) ≤B w
  ∧-≤-self false v = ≤-false
  ∧-≤-self true  v = true-greatest v

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
    ; ·-≤-self    = ∧-≤-self
    }

open BoolDM public using (BoolDM)

-- Dependent weight type: weights indexed by elements of a type A
-- W(A) represents a function A → W
module DependentWeight {ℓ} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- Weight function: assigns a weight to each element of type A
  WFun : Set ℓ → Set ℓ
  WFun A = A → W

  -- Constant weight function: same weight for all elements
  const-wf : ∀ {A : Set ℓ} → W → WFun A
  const-wf w _ = w

  -- Supremum of a weight function: upper bound over all values
  -- sup(w) = smallest v such that w(x) ≤ v for all x
  -- For finite types, this is just the maximum
  -- For general types, we need a postulate or work within a specific model
  postulate
    sup : ∀ {A : Set ℓ} → WFun A → W
    sup-upper : ∀ {A : Set ℓ} (wf : WFun A) (a : A) → wf a ≤ sup wf
    sup-least : ∀ {A : Set ℓ} (wf : WFun A) (v : W) →
                (∀ a → wf a ≤ v) → sup wf ≤ v

  -- Infimum of a weight function: lower bound over all values
  -- inf(w) = largest v such that v ≤ w(x) for all x
  postulate
    inf : ∀ {A : Set ℓ} → WFun A → W
    inf-lower : ∀ {A : Set ℓ} (wf : WFun A) (a : A) → inf wf ≤ wf a
    inf-greatest : ∀ {A : Set ℓ} (wf : WFun A) (v : W) →
                   (∀ a → v ≤ wf a) → v ≤ inf wf

  -- Pointwise multiplication of weight functions
  _·wf_ : ∀ {A : Set ℓ} → WFun A → WFun A → WFun A
  (wf₁ ·wf wf₂) a = wf₁ a · wf₂ a

  -- Pointwise negation of weight functions
  ¬wf : ∀ {A : Set ℓ} → WFun A → WFun A
  ¬wf wf a = ¬ (wf a)

  -- Key property: uniform weight is a special case of dependent weight
  -- sup(const w) = w and inf(const w) = w
  postulate
    sup-const : ∀ {A : Set ℓ} (w : W) → sup (const-wf {A = A} w) ≡ w
    inf-const : ∀ {A : Set ℓ} (w : W) → inf (const-wf {A = A} w) ≡ w

  -- Integration/expected value (for probabilistic interpretation)
  -- In the [0,1] model: ∫ w(x) dP(x) where P is the distribution over A
  -- For the abstract algebra, we use sup as the primary operation
  -- (integration requires additional structure like measure/summation)

-- De Morgan laws (derived)
module DeMorganLaws {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  private
    cong₂ : ∀ {A B C : Set ℓ} (f : A → B → C) {x y : A} {u v : B} →
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
