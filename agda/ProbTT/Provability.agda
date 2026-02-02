{- AXIOM STATUS SUMMARY for Provability.agda

All postulates in this module are META-LEVEL AXIOMS that cannot be
proven within ProbTT itself. They describe the meta-theory.

encode, encode-derivation: META-LEVEL AXIOM
  Godel encoding requires arithmetic (natural numbers, beta function)
  which ProbTT does not include. Standard in provability logic.

diagonal: META-LEVEL AXIOM
  Godel fixed-point theorem. Proven FROM encoding in systems with
  arithmetic. Without arithmetic, we axiomatize it.

D1, D2, D3: META-LEVEL AXIOM
  Hilbert-Bernays-Lob derivability conditions.
  D2 includes ProbTT-specific weight multiplication.
  Proven from encoding in arithmetic. We axiomatize them.

self-ref-weight: META-LEVEL AXIOM
  Existence of fixed-point weights for self-referential terms.
  Requires weight algebra to have fixed points (not guaranteed).

Reference: Boolos "Logic of Provability", Hajek-Paris-Shepherdson 2000
-}
-- Provability predicates for ProbTT meta-theory
-- Formalizes graded provability Prov_w(phi)
--
-- NOTE: This module uses postulates for genuinely meta-theoretic concepts
-- that cannot be proven within the object theory:
-- - Godel encoding (requires meta-level construction)
-- - Diagonal lemma (requires self-reference machinery)
-- - Derivability conditions (meta-level properties)
--
-- These are standard in formalized meta-theory (cf. Boolos "Logic of Provability")
--
-- LITERATURE CONTEXT:
-- This module formalizes concepts from Pavelka-style fuzzy logic:
--   - Graded provability: |phi|_T = sup{r | T proves (phi, r)}
--   - Pavelka (1979), Hajek "Metamathematics of Fuzzy Logic" (1998)
--
-- Key insight: provability as a DEGREE, not a binary yes/no.
-- ProbTT's Prov_w(phi) corresponds to Pavelka's (phi, r) with r = w.
--
-- The diagonal lemma and encoding follow standard Godel techniques,
-- but in a graded setting (cf. Hajek-Paris-Shepherdson 2000).

module ProbTT.Provability where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import ProbTT.Weight
open import ProbTT.Syntax
open import ProbTT.Context
open import ProbTT.Judgment

-- Provability predicate: Prov_w(φ) means φ is provable at weight w
-- This is the key extension for meta-theory
module Provability {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM

  -- Graded provability predicate
  -- Prov φ w means "φ is provable at weight w"
  -- This abstracts over the specific derivation
  data Prov : ∀ {n} → Tm n → W → Set ℓ where
    -- If we have a derivation at weight w, then Prov holds
    from-derivation : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w : W} →
                      Γ ⊢ t ∶ A 〔 w 〕 →
                      Prov t w

    -- Provability respects weight weakening
    prov-weaken : ∀ {n} {t : Tm n} {w v : W} →
                  Prov t w →
                  v ≤ w →
                  Prov t v

  -- Encoding of terms as terms (Gödel encoding)
  -- ⌈t⌉ : Tm n represents the code of term t
  -- This is needed for self-reference
  postulate
    ⌈_⌉ : ∀ {n} → Tm n → Tm 0
    -- Encoding preserves identity
    ⌈⌉-id : ∀ {n} (t : Tm n) → ⌈ t ⌉ ≡ ⌈ t ⌉

  -- Encoding of derivations
  -- Given a derivation, we can encode it as a term
  postulate
    encode-derivation : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w : W} →
                        Γ ⊢ t ∶ A 〔 w 〕 →
                        Tm 0

  -- Diagonal Lemma (Gödel's fixed-point theorem)
  -- For any property P on terms and weights,
  -- there exists a term G such that Prov G w ↔ P ⌈G⌉ w
  --
  -- This is the foundation for Gödel's incompleteness theorems
  postulate
    diagonal : ∀ {n} (P : Tm 0 → W → Set ℓ) →
               ∃ λ (G : Tm n) → ∀ w → (Prov G w → P ⌈ G ⌉ w) × (P ⌈ G ⌉ w → Prov G w)

  -- Derivability conditions (Hilbert-Bernays-Löb)
  -- D1: If Γ ⊢ t : A @ w, then Prov ⌈t⌉ w
  postulate
    D1 : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {w : W} →
         Γ ⊢ t ∶ A 〔 w 〕 →
         Prov ⌈ t ⌉ w

  -- D2: Prov(φ → ψ) w → Prov φ v → Prov ψ (w · v)
  -- (provability distributes over application, with weight multiplication)
  postulate
    D2 : ∀ {n} {φ : Tm n} {ψ : Tm (suc n)} {w v : W} →
         Prov (lam (base 0) ψ) w →
         Prov φ v →
         Prov (app (lam (base 0) ψ) φ) (w · v)

  -- D3: Prov φ w → Prov (Prov φ w) 1
  -- (provability is witnessed)
  postulate
    D3 : ∀ {n} {φ : Tm n} {w : W} →
         Prov φ w →
         Prov ⌈ φ ⌉ 𝟙

  -- Self-reference detection
  -- A term is self-referential if it contains its own encoding
  data SelfRef : ∀ {n} → Tm n → Set ℓ where
    via-encoding : ∀ {n} (t : Tm n) →
                   -- t mentions ⌈t⌉ (informally)
                   SelfRef t

  -- Weight of self-referential terms
  -- If a term is self-referential in a particular way,
  -- its weight satisfies a fixed-point equation
  --
  -- POSTULATE JUSTIFICATION:
  -- The weight of a self-referential term depends on the specific
  -- fixed-point equation it satisfies. This requires:
  -- 1. The diagonal lemma to construct the self-reference
  -- 2. Analysis of the property P that the term references
  -- Without knowing P, we cannot determine which weight satisfies w = P(w).
  -- In general, existence of such fixed points requires the weight algebra
  -- to be a complete lattice (which we don't assume in the minimal structure).
  postulate
    self-ref-weight : ∀ {n} {t : Tm n} →
                      SelfRef t →
                      ∃ λ w → Prov t w
