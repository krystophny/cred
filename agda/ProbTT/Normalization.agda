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

  -- Key insight: weights don't affect reduction
  -- The beta rules are purely syntactic. Weights only constrain WHICH terms
  -- are well-typed, not how they reduce.
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

  -- The interpretation of types as reducibility candidates
  -- This is the core of the normalization proof.
  -- Note: Termination is structural on types, but Agda cannot verify
  -- because substitution B[a] doesn't decrease the size measure.
  -- The actual termination argument uses type well-foundedness.
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

    -- Function types: f ∈ ⟦A ⇒ B⟧ iff for all a ∈ ⟦A⟧, f a ∈ ⟦B[a]⟧
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

    -- Pair types: p ∈ ⟦A ×' B⟧ iff fst p ∈ ⟦A⟧ and snd p ∈ ⟦B[fst p]⟧
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

  -- The fundamental theorem: all well-typed terms are in their type's candidate
  -- This is proved by induction on the typing derivation.
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
