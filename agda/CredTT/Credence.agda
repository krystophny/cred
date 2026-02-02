{- CREDTT CREDENCE ALGEBRA
   ========================

   AXIOM SUMMARY (following user's exact formalization):

   CORE CREDENCE ALGEBRA (CA):
   1. (W, ≤, 0, 1) bounded partial order (O1-O5)
   2. (W, ·, 1) commutative monoid with annihilator 0 (M1-M4)
   3. · monotone in each argument (M5)
   4. ¬ involutive antitone map swapping 0 and 1 (N1-N3)

   ω-ITERATION STRUCTURE (IT):
   5. ω-infimum operator infω : (ℕ → W) → W with glb laws (I1-I2)
   6. Scott continuity: w · infω(x) = infω(n → w · x(n)) (C1)

   EXPLICITLY EXCLUDED:
   - ARCH (Archimedean axiom): ∀s<1. infₙ(sⁿ) = 0
     This would collapse interior stability. CredTT does NOT assume this.
     ProbTT (real probability semantics) would add this as an extra axiom.

   KEY INSIGHT:
   Without ARCH, there can be idempotent elements e with e·e = e and 0 < e < 1.
   These give INTERIOR STABILITY - the core innovation of CredTT.
-}
module CredTT.Credence where

open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)

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

    -- Additional axioms for dynamics framework (4 axioms)
    -- Non-triviality: 0 and 1 are distinct
    𝟘≢𝟙 : 𝟘 ≡ 𝟙 → ⊥

    -- Negation is antitone: if c1 <= c2, then ~c2 <= ~c1
    ¬-antitone : ∀ {c₁ c₂} → c₁ ≤ c₂ → ¬ c₂ ≤ ¬ c₁

    -- Monotonicity of multiplication in both arguments
    ·-mono : ∀ {a b c d} → a ≤ c → b ≤ d → (a · b) ≤ (c · d)

    -- Positivity preservation: positive * positive = positive
    -- This ensures we are in a well-behaved algebra without zero divisors
    ·-positive : ∀ {c₁ c₂} → (𝟘 ≤ c₁) → (𝟘 ≡ c₁ → ⊥) → (𝟘 ≤ c₂) → (𝟘 ≡ c₂ → ⊥) →
                 (𝟘 ≤ (c₁ · c₂)) × (𝟘 ≡ (c₁ · c₂) → ⊥)

  -- Derived: De Morgan disjunction
  -- c ∨ d = ¬(¬c · ¬d)
  -- In [0,1]: c ∨ d = 1 - (1-c)(1-d) = c + d - cd
  _∨_ : C → C → C
  c ∨ d = ¬ (¬ c · ¬ d)

  -- Derived: left-monotonicity of multiplication (Issue #54)
  -- a ≤ b → a · c ≤ b · c
  ·-mono-l : ∀ {a b} c → a ≤ b → a · c ≤ b · c
  ·-mono-l c a≤b = ·-mono a≤b (≤-refl c)

  -- Derived: right-monotonicity of multiplication
  -- a ≤ b → c · a ≤ c · b
  ·-mono-r : ∀ {a b} c → a ≤ b → c · a ≤ c · b
  ·-mono-r c a≤b = ·-mono (≤-refl c) a≤b

  infixl 7 _·_
  infixl 6 _∨_
  infix  4 _≤_

-- ============================================================================
-- ω-ITERATION STRUCTURE
-- ============================================================================
-- This is the minimal extra structure needed for proof dynamics.
-- It allows talking about long proofs, recursion, and induction.
--
-- LIMITATION (Issue #131): No concrete instance for [0,1] is provided.
-- The IterationAlgebra record defines the INTERFACE (infω, continuity axioms)
-- but verifying that [0,1] with standard arithmetic satisfies these axioms
-- requires measure-theoretic arguments not formalized here.
-- BoolDM WOULD trivially satisfy this (finite sequences stabilize immediately),
-- but no BoolIterationAlgebra instance is implemented.

open import Data.Nat as Nat using (ℕ; zero; suc)

-- Record extending De Morgan algebra with ω-infima
record IterationAlgebra (ℓ : Level) : Set (Level.suc ℓ) where
  field
    -- Underlying De Morgan algebra
    algebra : DeMorganAlgebra ℓ

  open DeMorganAlgebra algebra public

  -- Sequences (ω-chains)
  Seq : Set ℓ
  Seq = ℕ → C

  field
    -- ω-infimum operator: greatest lower bound of a sequence
    infω : Seq → C

    -- (I1) Lower bound: infω(x) ≤ x(n) for all n
    infω-lower : ∀ (x : Seq) (n : ℕ) → infω x ≤ x n

    -- (I2) Greatest: if y ≤ x(n) for all n, then y ≤ infω(x)
    infω-greatest : ∀ (x : Seq) (y : C) → (∀ n → y ≤ x n) → y ≤ infω x

    -- (C1) Scott continuity: · distributes over ω-infima
    -- w · infω(x) = infω(n ↦ w · x(n))
    ·-infω-distrib : ∀ (w : C) (x : Seq) →
                     w · infω x ≡ infω (λ n → w · x n)

  -- Derived: ω-supremum via negation (De Morgan duality)
  supω : Seq → C
  supω x = ¬ (infω (λ n → ¬ (x n)))

  -- Powers: s⁰ = 1, s^(n+1) = sⁿ · s
  _^_ : C → ℕ → C
  s ^ zero    = 𝟙
  s ^ (suc n) = (s ^ n) · s

  -- Asymptotic credence under repeating step s:
  -- Iter(c, s) = infω(n ↦ c · sⁿ)
  Iter : C → C → C
  Iter c s = infω (λ n → c · (s ^ n))

  -- Stability under step s: Iter(c, s) > 0
  Stable : C → C → Set ℓ
  Stable c s = (Iter c s ≤ 𝟘 → ⊥) × (𝟘 ≤ Iter c s)

  -- Degeneration under step s: Iter(c, s) = 0
  Degenerate : C → C → Set ℓ
  Degenerate c s = Iter c s ≡ 𝟘

  -- Invariant under step: c = c · s
  Invariant : C → C → Set ℓ
  Invariant c s = c ≡ c · s

-- ============================================================================
-- ARCHIMEDEAN AXIOM (EXPLICITLY NOT INCLUDED IN CORE)
-- ============================================================================
-- This axiom would collapse interior stability. DO NOT assume it in CredTT!
-- ProbTT (probability semantics over [0,1]) would include this.
--
-- OPEN PROBLEM (Issue #108): Non-Archimedean model construction
-- The paper claims that non-Archimedean De Morgan algebras can have interior
-- idempotents (0 < e < 1 with e * e = e), but no concrete model is constructed.
-- Possible approaches:
--   1. Hyperreal interval [0,1]* with infinitesimals
--   2. Certain bounded complete distributive lattices
--   3. Tropical semiring under max-plus
-- Constructing such a model and proving its properties is future work.

module ArchimedeanAxiom {ℓ : Level} (IA : IterationAlgebra ℓ) where
  open IterationAlgebra IA

  -- ARCH: For all s < 1, infₙ(sⁿ) = 0
  -- This says "non-unit steps eventually degrade everything to zero"
  -- TRUE in [0,1] with real multiplication
  -- FALSE in algebras with interior idempotents
  ARCH : Set ℓ
  ARCH = ∀ (s : C) → (s ≤ 𝟙) → (s ≡ 𝟙 → ⊥) → infω (λ n → s ^ n) ≡ 𝟘

  -- With ARCH, only s = 1 preserves credence under iteration
  -- Without ARCH, interior fixed points are possible

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

  -- Non-triviality: false /= true
  false≢true : false ≡ true → ⊥
  false≢true ()

  -- Negation is antitone
  notB-antitone : ∀ {c₁ c₂} → c₁ ≤B c₂ → notB c₂ ≤B notB c₁
  notB-antitone {false} {false} _ = ≤B-refl true
  notB-antitone {false} {true}  _ = ≤-false
  notB-antitone {true}  {true}  _ = ≤B-refl false

  -- Multiplication is monotone
  -- Case analysis: a ≤B c means either a=false or c=true
  --                b ≤B d means either b=false or d=true
  -- Note: (a ∧B false) = false for any a, so use ≤-false
  ∧-mono : ∀ {a b c d} → a ≤B c → b ≤B d → (a ∧B b) ≤B (c ∧B d)
  ∧-mono {a}     {false} {c} {d} _       ≤-false with a
  ... | false = ≤-false  -- false ∧ false = false ≤ anything
  ... | true  = ≤-false  -- true ∧ false = false ≤ anything
  ∧-mono {false} {b}     {c} {d} ≤-false _       = ≤-false  -- false ∧ b = false ≤ anything
  ∧-mono {a}     {b}     {true} {true} ≤-true ≤-true = ≤-true  -- a ∧ b ≤ true ∧ true = true

  -- Positivity preservation: positive * positive = positive
  -- For Bool: c1 and c2 both positive means both are true, so c1 AND c2 is also true (positive)
  ∧-positive : ∀ {c₁ c₂} → (false ≤B c₁) → (false ≡ c₁ → ⊥) → (false ≤B c₂) → (false ≡ c₂ → ⊥) →
               (false ≤B (c₁ ∧B c₂)) × (false ≡ (c₁ ∧B c₂) → ⊥)
  ∧-positive {true}  {true}  _ _    _ _    = ≤-false , (λ ())
  ∧-positive {true}  {false} _ _    _ neq2 = ⊥-elim (neq2 refl)
  ∧-positive {false} {c₂}    _ neq1 _ _    = ⊥-elim (neq1 refl)

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
    ; 𝟘≢𝟙        = false≢true
    ; ¬-antitone  = notB-antitone
    ; ·-mono      = ∧-mono
    ; ·-positive  = ∧-positive
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

-- ============================================================================
-- NEGATION FIXPOINT STRUCTURE
-- ============================================================================
-- Some De Morgan algebras have a negation fixpoint c = ¬c (e.g., [0,1] has c = 1/2)
-- while others do not (e.g., Bool has no such element).
-- This module defines the predicate and documents which algebras have it.

module NegationFixpointStructure {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM

  -- A negation fixpoint is an element c such that ¬c = c
  NegationFixpoint : C → Set ℓ
  NegationFixpoint c = ¬ c ≡ c

  -- Predicate: an algebra has a negation fixpoint
  -- This is a PROPERTY of the algebra, not assumed in the base DeMorganAlgebra
  HasNegationFixpoint : Set ℓ
  HasNegationFixpoint = Σ C NegationFixpoint
    where open import Data.Product using (Σ)

  -- Predicate: an algebra has a UNIQUE negation fixpoint
  HasUniqueNegationFixpoint : Set ℓ
  HasUniqueNegationFixpoint = HasNegationFixpoint × (∀ c d → NegationFixpoint c → NegationFixpoint d → c ≡ d)
    where open import Data.Product using (Σ; _×_)

-- ============================================================================
-- BOOL DOES NOT HAVE A NEGATION FIXPOINT
-- ============================================================================
-- This is important: the Bool algebra (classical logic) has no c = not c.
-- This is WHY classical Gödel sentences are "undecidable" rather than having
-- a determinate intermediate credence.

module BoolNoNegationFixpoint where
  open BoolDM
  open NegationFixpointStructure BoolDM

  -- Direct proof: neither true nor false satisfies not c = c
  no-bool-fixpoint : ∀ (b : Bool) → NegationFixpoint b → ⊥
  no-bool-fixpoint false ()
  no-bool-fixpoint true ()

  -- Consequence: Bool does not have a negation fixpoint
  bool-no-HasNegationFixpoint : HasNegationFixpoint → ⊥
  bool-no-HasNegationFixpoint (c , fp) = no-bool-fixpoint c fp
    where open import Data.Product using (_,_)

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
