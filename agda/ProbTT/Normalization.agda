-- Normalization for ProbTT via Tait-style logical relations
--
-- ============================================================================
-- AXIOM STATUS SUMMARY
-- ============================================================================
--
-- This module contains a SKETCH of the normalization proof for ProbTT.
-- The structure follows standard Tait-style logical relations (reducibility
-- candidates), but several lemmas are postulated rather than proven.
--
-- POSTULATE CATEGORIES:
--
-- 1. TERMINATING PRAGMA (line ~153)
--    Status: ACCEPTABLE with justification
--    Reason: Termination holds by well-founded induction on type structure.
--    Agda cannot verify because substitution B[a] does not syntactically
--    decrease type size. The true termination argument uses:
--      - Types are well-founded under subterm ordering
--      - B[a] has the same TYPE COMPLEXITY as B (substitution preserves structure)
--      - The recursive calls are on strict subterms of the original type
--    A proper fix would use sized types or well-founded recursion combinators.
--
-- 2. REDUCIBILITY CANDIDATE LEMMAS (postulate-fun-*, postulate-pair-*)
--    Status: SHOULD BE PROVEN
--    Reason: These are standard lemmas in Tait-style normalization proofs.
--    They are provable but require careful reasoning about:
--      - Reducibility at function types (Girard's method)
--      - Backward closure under reduction
--      - Neutral term inclusion
--    References: Girard "Proofs and Types", Ch. 6; Harper PFPL Ch. 47
--
-- 3. FUNDAMENTAL THEOREM LEMMAS (postulate-lam-fundamental, etc.)
--    Status: SHOULD BE PROVEN
--    Reason: These establish that well-typed terms inhabit their semantic
--    interpretations. They follow from the typing rules and the definition
--    of reducibility candidates. Standard but tedious induction.
--
-- 4. WEIGHT-IRRELEVANT-REDUCTION
--    Status: SHOULD BE PROVEN
--    Reason: This states that reduction preserves typability (subject
--    reduction). It is a standard metatheorem and depends on the
--    substitution lemma from Properties.agda.
--
-- KEY INSIGHT: Weights do not affect reduction
-- The beta rules are purely syntactic. Weights only determine WHICH terms
-- are well-typed, not how they reduce. Therefore, normalization in ProbTT
-- is identical to normalization in MLTT.
--
-- ============================================================================

module ProbTT.Normalization where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_)
open import Data.Fin as Fin using (Fin)
open import Data.Product using (_×_; proj₁; proj₂; Σ; ∃) renaming (_,_ to _P,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Induction.WellFounded using (WellFounded; Acc; acc)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Substitution
open import ProbTT.Context
open import ProbTT.Judgment

module Normalization {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM

  -- Neutral and normal forms (beta-normal)
  -- Weights don't affect the syntactic structure, only the typing derivations.
  -- Therefore, normal forms in ProbTT are identical to MLTT.
  mutual
    data Neutral : ∀ {n} -> Tm n -> Set where
      ne-var  : ∀ {n} (i : Fin n) -> Neutral (var i)
      ne-app  : ∀ {n} {f a : Tm n} -> Neutral f -> Normal a -> Neutral (app f a)
      ne-fst  : ∀ {n} {t : Tm n} -> Neutral t -> Neutral (fst t)
      ne-snd  : ∀ {n} {t : Tm n} -> Neutral t -> Neutral (snd t)
      ne-case : ∀ {n} {e : Tm n} {l r : Tm (suc n)} ->
                Neutral e -> Normal l -> Normal r -> Neutral (case e l r)
      ne-J    : ∀ {n} {M : Ty (suc (suc n))} {d p : Tm n} ->
                Neutral p -> Normal d -> Neutral (J M d p)

    data Normal : ∀ {n} -> Tm n -> Set where
      nf-ne   : ∀ {n} {t : Tm n} -> Neutral t -> Normal t
      nf-lam  : ∀ {n} {A : Ty n} {t : Tm (suc n)} -> Normal t -> Normal (lam A t)
      nf-pair : ∀ {n} {a b : Tm n} -> Normal a -> Normal b -> Normal (pair a b)
      nf-inl  : ∀ {n} {a : Tm n} -> Normal a -> Normal (inl a)
      nf-inr  : ∀ {n} {b : Tm n} -> Normal b -> Normal (inr b)
      nf-refl : ∀ {n} -> Normal {n} refl'

  -- Single-step beta reduction
  data _⟶_ : ∀ {n} -> Tm n -> Tm n -> Set where
    -- Beta rules
    β-Π : ∀ {n} {A : Ty n} {b : Tm (suc n)} {a : Tm n} ->
          app (lam A b) a ⟶ (b [ a ])
    β-Σ₁ : ∀ {n} {a b : Tm n} ->
           fst (pair a b) ⟶ a
    β-Σ₂ : ∀ {n} {a b : Tm n} ->
           snd (pair a b) ⟶ b
    β-+-inl : ∀ {n} {a : Tm n} {l r : Tm (suc n)} ->
              case (inl a) l r ⟶ (l [ a ])
    β-+-inr : ∀ {n} {b : Tm n} {l r : Tm (suc n)} ->
              case (inr b) l r ⟶ (r [ b ])
    β-Id : ∀ {n} {M : Ty (suc (suc n))} {d : Tm n} ->
           J M d refl' ⟶ d

    -- Congruence rules
    ξ-app₁ : ∀ {n} {f f' a : Tm n} ->
             f ⟶ f' ->
             app f a ⟶ app f' a
    ξ-app₂ : ∀ {n} {f a a' : Tm n} ->
             a ⟶ a' ->
             app f a ⟶ app f a'
    ξ-lam : ∀ {n} {A : Ty n} {t t' : Tm (suc n)} ->
            t ⟶ t' ->
            lam A t ⟶ lam A t'
    ξ-pair₁ : ∀ {n} {a a' b : Tm n} ->
              a ⟶ a' ->
              pair a b ⟶ pair a' b
    ξ-pair₂ : ∀ {n} {a b b' : Tm n} ->
              b ⟶ b' ->
              pair a b ⟶ pair a b'
    ξ-fst : ∀ {n} {t t' : Tm n} ->
            t ⟶ t' ->
            fst t ⟶ fst t'
    ξ-snd : ∀ {n} {t t' : Tm n} ->
            t ⟶ t' ->
            snd t ⟶ snd t'
    ξ-inl : ∀ {n} {a a' : Tm n} ->
            a ⟶ a' ->
            inl a ⟶ inl a'
    ξ-inr : ∀ {n} {b b' : Tm n} ->
            b ⟶ b' ->
            inr b ⟶ inr b'
    ξ-case₁ : ∀ {n} {e e' : Tm n} {l r : Tm (suc n)} ->
              e ⟶ e' ->
              case e l r ⟶ case e' l r
    ξ-case₂ : ∀ {n} {e : Tm n} {l l' r : Tm (suc n)} ->
              l ⟶ l' ->
              case e l r ⟶ case e l' r
    ξ-case₃ : ∀ {n} {e : Tm n} {l r r' : Tm (suc n)} ->
              r ⟶ r' ->
              case e l r ⟶ case e l r'
    ξ-J₁ : ∀ {n} {M : Ty (suc (suc n))} {d d' p : Tm n} ->
           d ⟶ d' ->
           J M d p ⟶ J M d' p
    ξ-J₂ : ∀ {n} {M : Ty (suc (suc n))} {d p p' : Tm n} ->
           p ⟶ p' ->
           J M d p ⟶ J M d p'

  -- Multi-step reduction (reflexive-transitive closure)
  data _⟶*_ : ∀ {n} -> Tm n -> Tm n -> Set where
    refl* : ∀ {n} {t : Tm n} -> t ⟶* t
    step* : ∀ {n} {t t' t'' : Tm n} ->
            t ⟶ t' ->
            t' ⟶* t'' ->
            t ⟶* t''

  -- Normal form: no further reduction possible
  IsNormal : ∀ {n} -> Tm n -> Set
  IsNormal t = ∀ {t'} -> NotRed (t ⟶ t')
    where NotRed : Set -> Set
          NotRed A = A -> ⊥

  -- Weak normalization: every term reduces to a normal form
  WeaklyNormalizing : ∀ {n} -> Tm n -> Set
  WeaklyNormalizing t = ∃ λ nf -> (t ⟶* nf) × Normal nf

  -- =========================================================================
  -- POSTULATE: Subject Reduction (weight-irrelevant-reduction)
  -- Status: SHOULD BE PROVEN (depends on substitution lemma)
  -- =========================================================================
  --
  -- This states that if t reduces to t' and t is well-typed, then t' is
  -- well-typed (possibly at a different weight). This is the subject
  -- reduction theorem.
  --
  -- Why possibly different weight: Consider (lam A b) applied to a.
  -- If lam A b : A -> B @ w and a : A @ v, then (lam A b) a : B @ w*v.
  -- After beta reduction, b[a] : B[a] @ w*v (same weight).
  -- But the reduction itself does not change the weight.
  --
  -- Proof sketch: Case analysis on the reduction rule.
  -- Each beta rule preserves typing by the substitution lemma.
  -- Congruence rules follow by induction.
  --
  -- Dependency: Properties.agda subst-typed
  -- =========================================================================
  postulate
    weight-irrelevant-reduction : ∀ {n} {t t' : Tm n} {Γ : Ctx n} {A : Ty n} {w : W} ->
      (t ⟶ t') -> Γ ⊢ t ∶ A 〔 w 〕 -> ∃ λ w' -> Γ ⊢ t' ∶ A 〔 w' 〕

  -- Logical relations for normalization proof
  -- We use Tait's method: define a logical predicate on types
  -- and show all well-typed terms satisfy it.

  -- Reducibility candidates (semantic types)
  -- A reducibility candidate R for a type A is a set of terms such that:
  -- 1. All terms in R are normalizing
  -- 2. R is closed under expansion (if t' ∈ R and t ⟶ t', then t ∈ R)
  -- 3. Neutral terms of the right type are in R
  record Candidate {n : ℕ} (A : Ty n) : Set₁ where
    field
      carrier : Tm n -> Set
      normalizing : ∀ {t} -> carrier t -> WeaklyNormalizing t
      backward-closed : ∀ {t t'} -> t ⟶ t' -> carrier t' -> carrier t
      neutral-in : ∀ {t} -> Neutral t -> carrier t

  -- =========================================================================
  -- TERMINATING PRAGMA JUSTIFICATION
  -- Status: ACCEPTABLE (termination holds but Agda cannot verify)
  -- =========================================================================
  --
  -- The interpretation function is structurally recursive on types.
  -- Agda cannot verify termination because:
  --   1. In the function case (A => B), we recurse on B[a] for arbitrary a
  --   2. Syntactically, B[a] is not a subterm of (A => B)
  --
  -- Why termination DOES hold:
  --   1. Type STRUCTURE is preserved by substitution
  --      - B[a] has exactly the same type formers as B
  --      - The substitution only affects term components (in Id types)
  --   2. The recursive calls are on strict structural subterms:
  --      - For A => B, we recurse on A and (structurally) B
  --      - For A x B, we recurse on A and B
  --      - For A + B, we recurse on A and B
  --      - For Id A a b, we recurse on A (terms a,b do not affect recursion)
  --   3. Base types are the base case with no recursion
  --
  -- Proper fix: Use sized types or well-founded recursion on type complexity.
  -- The complexity measure is:
  --   |base i|     = 0
  --   |A => B|     = 1 + max(|A|, |B|)
  --   |A x B|      = 1 + max(|A|, |B|)
  --   |A + B|      = 1 + max(|A|, |B|)
  --   |Id A a b|   = 1 + |A|
  --
  -- This measure is preserved by term substitution and strictly decreases
  -- in all recursive calls.
  --
  -- Reference: Harper PFPL Ch. 47, Abel "Normalization by Evaluation"
  -- =========================================================================
  {-# TERMINATING #-}
  mutual
    ⟦_⟧ : ∀ {n} (A : Ty n) -> Candidate A
    ⟦ base i ⟧ = record
      { carrier = λ t -> WeaklyNormalizing t
      ; normalizing = λ x -> x
      ; backward-closed = λ step (nf P, red P, norm) -> nf P, step* step red P, norm
      ; neutral-in = λ {t} ne -> t P, refl* P, nf-ne ne
      }
    ⟦ A ⇒ B ⟧ = fun-candidate A B
    ⟦ A ×' B ⟧ = pair-candidate A B
    ⟦ A +' B ⟧ = sum-candidate A B
    ⟦ Id A a b ⟧ = id-candidate A a b

    -- =========================================================================
    -- POSTULATES: Reducibility Candidate Properties for Function Types
    -- Status: SHOULD BE PROVEN (standard Tait-style lemmas)
    -- =========================================================================
    --
    -- These three lemmas establish that the function type interpretation
    -- forms a valid reducibility candidate. They are standard in the
    -- literature but require careful reasoning.
    --
    -- postulate-fun-normalizing:
    --   If f satisfies the functional property (applies well to all reducible
    --   arguments), then f normalizes. Proof: apply f to a fresh variable,
    --   use that application normalizes, extract that f normalizes.
    --
    -- postulate-fun-backward:
    --   Backward closure under reduction. If f reduces to f' and f' is
    --   reducible, then f is reducible. Proof: for any reducible a,
    --   (app f a) reduces to (app f' a) which is reducible, so (app f a)
    --   is reducible by backward closure at the result type.
    --
    -- postulate-fun-neutral:
    --   Neutral terms are reducible. Proof: for any reducible a, (app f a)
    --   is neutral (since f is neutral), hence reducible by the neutral
    --   inclusion property at the result type.
    --
    -- Reference: Girard "Proofs and Types" Ch. 6, Tait's method
    -- =========================================================================
    fun-candidate : ∀ {n} (A : Ty n) (B : Ty (suc n)) -> Candidate (A ⇒ B)
    fun-candidate {n} A B = record
      { carrier = carrier-fun
      ; normalizing = postulate-fun-normalizing
      ; backward-closed = postulate-fun-backward
      ; neutral-in = postulate-fun-neutral
      }
      where
        carrier-fun : Tm n -> Set
        carrier-fun f = ∀ a -> Candidate.carrier ⟦ A ⟧ a -> Candidate.carrier ⟦ B [ a ]ₜ ⟧ (app f a)
        postulate
          postulate-fun-normalizing : ∀ {f} -> carrier-fun f -> WeaklyNormalizing f
          postulate-fun-backward : ∀ {f f'} -> f ⟶ f' -> carrier-fun f' -> carrier-fun f
          postulate-fun-neutral : ∀ {f} -> Neutral f -> carrier-fun f

    -- =========================================================================
    -- POSTULATES: Reducibility Candidate Properties for Pair Types
    -- Status: SHOULD BE PROVEN (standard Tait-style lemmas)
    -- =========================================================================
    --
    -- Similar to function types, these establish that pairs form a valid
    -- reducibility candidate.
    --
    -- postulate-pair-normalizing:
    --   If both projections are reducible, the pair normalizes.
    --   Proof: fst p and snd p normalize, so p normalizes (pairs normalize
    --   iff both components normalize).
    --
    -- postulate-pair-backward:
    --   Backward closure. If p reduces to p' and p' is reducible, then p
    --   is reducible. Proof: fst p reduces to fst p' (congruence), and
    --   fst p' is reducible, so fst p is reducible by backward closure.
    --   Similarly for snd.
    --
    -- postulate-pair-neutral:
    --   Neutral pairs are reducible. Proof: fst p and snd p are neutral
    --   (since p is neutral), hence reducible.
    --
    -- Reference: Harper PFPL Ch. 47
    -- =========================================================================
    pair-candidate : ∀ {n} (A : Ty n) (B : Ty (suc n)) -> Candidate (A ×' B)
    pair-candidate {n} A B = record
      { carrier = carrier-pair
      ; normalizing = postulate-pair-normalizing
      ; backward-closed = postulate-pair-backward
      ; neutral-in = postulate-pair-neutral
      }
      where
        carrier-pair : Tm n -> Set
        carrier-pair p = Candidate.carrier ⟦ A ⟧ (fst p) × Candidate.carrier ⟦ B [ fst p ]ₜ ⟧ (snd p)
        postulate
          postulate-pair-normalizing : ∀ {p} -> carrier-pair p -> WeaklyNormalizing p
          postulate-pair-backward : ∀ {p p'} -> p ⟶ p' -> carrier-pair p' -> carrier-pair p
          postulate-pair-neutral : ∀ {p} -> Neutral p -> carrier-pair p

    -- Sum types: s ∈ ⟦A +' B⟧ iff case analysis normalizes
    sum-candidate : ∀ {n} (A B : Ty n) -> Candidate (A +' B)
    sum-candidate A B = record
      { carrier = λ s -> WeaklyNormalizing s
      ; normalizing = λ x -> x
      ; backward-closed = λ step (nf P, red P, norm) -> nf P, step* step red P, norm
      ; neutral-in = λ {t} ne -> t P, refl* P, nf-ne ne
      }

    -- Identity types: p ∈ ⟦Id A a b⟧ iff p normalizes
    id-candidate : ∀ {n} (A : Ty n) (a b : Tm n) -> Candidate (Id A a b)
    id-candidate A a b = record
      { carrier = λ p -> WeaklyNormalizing p
      ; normalizing = λ x -> x
      ; backward-closed = λ step (nf P, red P, norm) -> nf P, step* step red P, norm
      ; neutral-in = λ {t} ne -> t P, refl* P, nf-ne ne
      }

  -- =========================================================================
  -- FUNDAMENTAL THEOREM: Well-typed terms are reducible
  -- =========================================================================
  --
  -- This is the main lemma of Tait-style normalization. It states that
  -- every well-typed term belongs to the reducibility candidate for its type.
  --
  -- The proof proceeds by induction on the typing derivation. Most cases
  -- are straightforward, but several require auxiliary lemmas that are
  -- postulated here.
  --
  -- =========================================================================
  -- POSTULATES IN FUNDAMENTAL THEOREM
  -- Status: SHOULD BE PROVEN (standard but require infrastructure)
  -- =========================================================================
  --
  -- postulate-lam-fundamental:
  --   For lambda abstractions, we need to show that (app (lam A b) a) is
  --   reducible when a is reducible. This requires:
  --   1. Beta reduction: (app (lam A b) a) reduces to b[a]
  --   2. Substitution lemma: b[a] is well-typed
  --   3. IH: b[a] is reducible (induction on typing derivation)
  --   4. Backward closure: since b[a] is reducible and (lam A b) a reduces
  --      to it, (lam A b) a is reducible
  --
  -- postulate-pair-fundamental:
  --   For pairs, we need fst (pair a b) and snd (pair a b) reducible.
  --   This requires backward closure: fst (pair a b) reduces to a,
  --   and a is reducible by IH.
  --
  -- postulate-sum-fundamental-inl/inr:
  --   For injections, we need inl a (or inr b) to normalize.
  --   This follows because a normalizes and Normal is preserved by inl.
  --
  -- postulate-case-fundamental:
  --   For case analysis, we need case e l r to normalize.
  --   This requires analyzing whether e is neutral or canonical.
  --
  -- postulate-refl-fundamental:
  --   For reflexivity, refl is normal, hence trivially reducible.
  --
  -- postulate-J-fundamental:
  --   For J elimination, we need J M d p to normalize.
  --   This requires analyzing whether p is neutral or refl.
  --
  -- =========================================================================
  fundamental : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w : W} ->
                Γ ⊢ t ∶ A 〔 w 〕 ->
                Candidate.carrier ⟦ A ⟧ t
  fundamental {Γ = Γ} (t-var i) = Candidate.neutral-in ⟦ lookup Γ i ⟧ (ne-var i)
  fundamental (t-weaken d _) = fundamental d
  fundamental (t-lam {A = A} {B = B} d) = λ a a∈ ->
    postulate-lam-fundamental a d a∈
    where
      postulate
        postulate-lam-fundamental : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {b : Tm (suc n)} {w : W} (a : Tm n) ->
          (Γ , A) ⊢ b ∶ B 〔 w 〕 -> Candidate.carrier ⟦ A ⟧ a -> Candidate.carrier ⟦ B [ a ]ₜ ⟧ (app (lam A b) a)
  fundamental (t-app {a = a} df da) =
    let f∈ = fundamental df
        a∈ = fundamental da
    in f∈ a a∈
  fundamental (t-pair da db) =
    postulate-pair-fundamental da db
    where
      postulate
        postulate-pair-fundamental : ∀ {n} {Γ : Ctx n} {A : Ty n} {B : Ty (suc n)} {a b : Tm n} {w v : W} ->
          Γ ⊢ a ∶ A 〔 w 〕 -> Γ ⊢ b ∶ (B [ a ]ₜ) 〔 v 〕 ->
          Candidate.carrier ⟦ A ⟧ (fst (pair a b)) × Candidate.carrier ⟦ B [ fst (pair a b) ]ₜ ⟧ (snd (pair a b))
  fundamental (t-fst d) = proj₁ (fundamental d)
  fundamental (t-snd d) = proj₂ (fundamental d)
  fundamental (t-inl {A = A} {B = B} d) = postulate-sum-fundamental-inl A B (fundamental d)
    where
      postulate
        postulate-sum-fundamental-inl : ∀ {n} (A B : Ty n) {a : Tm n} ->
          Candidate.carrier ⟦ A ⟧ a -> Candidate.carrier ⟦ A +' B ⟧ (inl a)
  fundamental (t-inr {A = A} {B = B} d) = postulate-sum-fundamental-inr A B (fundamental d)
    where
      postulate
        postulate-sum-fundamental-inr : ∀ {n} (A B : Ty n) {b : Tm n} ->
          Candidate.carrier ⟦ B ⟧ b -> Candidate.carrier ⟦ A +' B ⟧ (inr b)
  fundamental (t-case de dl dr) =
    postulate-case-fundamental de dl dr
    where
      postulate
        postulate-case-fundamental : ∀ {n} {Γ : Ctx n} {A B C : Ty n} {e : Tm n} {l r : Tm (suc n)} {w v : W} ->
          Γ ⊢ e ∶ (A +' B) 〔 w 〕 -> (Γ , A) ⊢ l ∶ wkTy C 〔 v 〕 -> (Γ , B) ⊢ r ∶ wkTy C 〔 v 〕 ->
          Candidate.carrier ⟦ C ⟧ (case e l r)
  fundamental (t-refl {A = A} {a = a} d) =
    postulate-refl-fundamental A a (fundamental d)
    where
      postulate
        postulate-refl-fundamental : ∀ {n} (A : Ty n) (a : Tm n) ->
          Candidate.carrier ⟦ A ⟧ a -> Candidate.carrier ⟦ Id A a a ⟧ refl'
  fundamental (t-J dp dd) =
    postulate-J-fundamental dp dd
    where
      postulate
        postulate-J-fundamental : ∀ {n} {Γ : Ctx n} {A : Ty n} {a b : Tm n} {M : Ty (suc (suc n))} {d p : Tm n} {w v : W} ->
          Γ ⊢ p ∶ Id A a b 〔 w 〕 -> Γ ⊢ d ∶ (M [ refl' , a ]₂ₜ) 〔 v 〕 ->
          Candidate.carrier ⟦ M [ p , b ]₂ₜ ⟧ (J M d p)

  -- Main theorem: weak normalization for all well-typed terms
  weak-normalization : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w : W} ->
                       Γ ⊢ t ∶ A 〔 w 〕 ->
                       WeaklyNormalizing t
  weak-normalization {A = A} d = Candidate.normalizing ⟦ A ⟧ (fundamental d)

  -- Corollary: weights don't affect normalization
  -- A term normalizes in ProbTT iff it normalizes in MLTT.
  -- This is because reduction is purely syntactic.
  weight-independent-normalization : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w w' : W} ->
                                     Γ ⊢ t ∶ A 〔 w 〕 ->
                                     Γ ⊢ t ∶ A 〔 w' 〕 ->
                                     WeaklyNormalizing t
  weight-independent-normalization d _ = weak-normalization d
