{- AXIOM STATUS SUMMARY for Credence.agda (DependentCredence module)

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
module CredTT.Credence where

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
    C : Set ℓ
    𝟘 : C
    𝟙 : C
    _·_ : C → C → C
    ¬_ : C → C
    _≤_ : C → C → Set ℓ

    -- Multiplication axioms (6)
    ·-identityʳ : ∀ c → c · 𝟙 ≡ c
    ·-identityˡ : ∀ c → 𝟙 · c ≡ c
    ·-annihilʳ  : ∀ c → c · 𝟘 ≡ 𝟘
    ·-annihilˡ  : ∀ c → 𝟘 · c ≡ 𝟘
    ·-assoc     : ∀ a b c → (a · b) · c ≡ a · (b · c)
    ·-comm      : ∀ a b → a · b ≡ b · a

    -- Complement axioms (3)
    ¬-𝟘    : ¬ 𝟘 ≡ 𝟙
    ¬-𝟙    : ¬ 𝟙 ≡ 𝟘
    ¬-invol : ∀ c → ¬ (¬ c) ≡ c

    -- Order axioms (6)
    ≤-refl     : ∀ c → c ≤ c
    ≤-trans    : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    ≤-antisym  : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
    𝟘-least    : ∀ c → 𝟘 ≤ c
    𝟙-greatest : ∀ c → c ≤ 𝟙
    ·-≤-self   : ∀ c d → c · d ≤ c  -- multiplication decreases (c·d ≤ c)

  -- Derived: De Morgan disjunction
  -- c ∨ d = ¬(¬c · ¬d)
  -- In [0,1]: c ∨ d = 1 - (1-c)(1-d) = c + d - cd
  _∨_ : C → C → C
  c ∨ d = ¬ (¬ c · ¬ d)

  infixl 7 _·_
  infixl 6 _∨_
  infix  4 _≤_

-- Boolean De Morgan algebra: the {0,1} case
-- This is what gives us MLTT when used as credences
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
  ∧-identityʳ : ∀ c → c ∧B true ≡ c
  ∧-identityʳ false = refl
  ∧-identityʳ true  = refl

  ∧-identityˡ : ∀ c → true ∧B c ≡ c
  ∧-identityˡ c = refl

  ∧-annihilʳ : ∀ c → c ∧B false ≡ false
  ∧-annihilʳ false = refl
  ∧-annihilʳ true  = refl

  ∧-annihilˡ : ∀ c → false ∧B c ≡ false
  ∧-annihilˡ c = refl

  ∧-assoc : ∀ a b c → (a ∧B b) ∧B c ≡ a ∧B (b ∧B c)
  ∧-assoc false b c = refl
  ∧-assoc true  b c = refl

  ∧-comm : ∀ a b → a ∧B b ≡ b ∧B a
  ∧-comm false false = refl
  ∧-comm false true  = refl
  ∧-comm true  false = refl
  ∧-comm true  true  = refl

  -- Proofs of complement axioms
  not-false : notB false ≡ true
  not-false = refl

  not-true : notB true ≡ false
  not-true = refl

  not-invol : ∀ c → notB (notB c) ≡ c
  not-invol false = refl
  not-invol true  = refl

  -- Proofs of order axioms
  ≤B-refl : ∀ c → c ≤B c
  ≤B-refl false = ≤-false
  ≤B-refl true  = ≤-true

  ≤B-trans : ∀ {a b c} → a ≤B b → b ≤B c → a ≤B c
  ≤B-trans ≤-false _       = ≤-false
  ≤B-trans ≤-true  ≤-true  = ≤-true

  ≤B-antisym : ∀ {a b} → a ≤B b → b ≤B a → a ≡ b
  ≤B-antisym ≤-false ≤-false = refl
  ≤B-antisym ≤-true  ≤-true  = refl

  false-least : ∀ c → false ≤B c
  false-least c = ≤-false

  true-greatest : ∀ c → c ≤B true
  true-greatest c = ≤-true

  -- Multiplication decreases: c ∧ d ≤ c
  ∧-≤-self : ∀ c d → (c ∧B d) ≤B c
  ∧-≤-self false d = ≤-false
  ∧-≤-self true  d = true-greatest d

  -- The complete Boolean De Morgan algebra
  BoolDM : DeMorganAlgebra _
  BoolDM = record
    { C           = Bool
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

-- Dependent credence type: credences indexed by elements of a type A
-- C(A) represents a function A -> C
module DependentCredence {ℓ} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- Credence function: assigns a credence to each element of type A
  CFun : Set ℓ → Set ℓ
  CFun A = A → C

  -- Constant credence function: same credence for all elements
  const-cf : ∀ {A : Set ℓ} → C → CFun A
  const-cf c _ = c

  -- Supremum of a credence function: upper bound over all values
  -- sup(c) = smallest d such that c(x) ≤ d for all x
  -- For finite types, this is just the maximum
  -- For general types, we need a postulate or work within a specific model
  postulate
    sup : ∀ {A : Set ℓ} → CFun A → C
    sup-upper : ∀ {A : Set ℓ} (cf : CFun A) (a : A) → cf a ≤ sup cf
    sup-least : ∀ {A : Set ℓ} (cf : CFun A) (d : C) →
                (∀ a → cf a ≤ d) → sup cf ≤ d

  -- Infimum of a credence function: lower bound over all values
  -- inf(c) = largest d such that d ≤ c(x) for all x
  postulate
    inf : ∀ {A : Set ℓ} → CFun A → C
    inf-lower : ∀ {A : Set ℓ} (cf : CFun A) (a : A) → inf cf ≤ cf a
    inf-greatest : ∀ {A : Set ℓ} (cf : CFun A) (d : C) →
                   (∀ a → d ≤ cf a) → d ≤ inf cf

  -- Pointwise multiplication of credence functions
  _·cf_ : ∀ {A : Set ℓ} → CFun A → CFun A → CFun A
  (cf₁ ·cf cf₂) a = cf₁ a · cf₂ a

  -- Pointwise negation of credence functions
  ¬cf : ∀ {A : Set ℓ} → CFun A → CFun A
  ¬cf cf a = ¬ (cf a)

  -- Key property: uniform credence is a special case of dependent credence
  -- sup(const c) = c and inf(const c) = c
  postulate
    sup-const : ∀ {A : Set ℓ} (c : C) → sup (const-cf {A = A} c) ≡ c
    inf-const : ∀ {A : Set ℓ} (c : C) → inf (const-cf {A = A} c) ≡ c

  -- Integration/expected value (for probabilistic interpretation)
  -- In the [0,1] model: integral of c(x) dP(x) where P is the distribution over A
  -- For the abstract algebra, we use sup as the primary operation
  -- (integration requires additional structure like measure/summation)

-- De Morgan laws (derived)
module DeMorganLaws {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  private
    cong₂ : ∀ {A B D : Set ℓ} (f : A → B → D) {x y : A} {u v : B} →
            x ≡ y → u ≡ v → f x u ≡ f y v
    cong₂ f refl refl = refl

  -- ¬(c · d) = ¬c ∨ ¬d
  -- By definition: ¬c ∨ ¬d = ¬(¬¬c · ¬¬d) = ¬(c · d)
  demorgan-· : ∀ c d → ¬ (c · d) ≡ (¬ c) ∨ (¬ d)
  demorgan-· c d = cong ¬_ (sym (cong₂ _·_ (¬-invol c) (¬-invol d)))

  -- ¬(c ∨ d) = ¬c · ¬d
  -- ¬(c ∨ d) = ¬¬(¬c · ¬d) = ¬c · ¬d
  demorgan-∨ : ∀ c d → ¬ (c ∨ d) ≡ (¬ c) · (¬ d)
  demorgan-∨ c d = ¬-invol (¬ c · ¬ d)
