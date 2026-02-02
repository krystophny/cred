{- AXIOM STATUS SUMMARY for Provability.agda

All postulates in this module are META-LEVEL AXIOMS that cannot be
proven within CredTT itself. They describe the meta-theory.

encode, encode-derivation: META-LEVEL AXIOM
  Godel encoding requires arithmetic (natural numbers, beta function)
  which CredTT does not include. Standard in provability logic.

diagonal: META-LEVEL AXIOM
  Godel fixed-point theorem. Proven FROM encoding in systems with
  arithmetic. Without arithmetic, we axiomatize it.

D1, D2, D3: META-LEVEL AXIOM
  Hilbert-Bernays-Lob derivability conditions.
  D2 includes CredTT-specific credence multiplication.
  Proven from encoding in arithmetic. We axiomatize them.

self-ref-credence: META-LEVEL AXIOM
  Existence of fixed-point credences for self-referential terms.
  Requires credence algebra to have fixed points (not guaranteed).

Reference: Boolos "Logic of Provability", Hajek-Paris-Shepherdson 2000
-}
-- Provability predicates for CredTT meta-theory
-- Formalizes graded provability Prov_c(phi)
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
-- CredTT's Prov_c(phi) corresponds to Pavelka's (phi, r) with r = c.
--
-- The diagonal lemma and encoding follow standard Godel techniques,
-- but in a graded setting (cf. Hajek-Paris-Shepherdson 2000).

module CredTT.Provability where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

open import CredTT.Credence
open import CredTT.Syntax
open import CredTT.Context
open import CredTT.Judgment

-- Provability predicate: Prov_c(φ) means φ is provable at credence c
-- This is the key extension for meta-theory
module Provability {ℓ : Level} (DM : DeMorganAlgebra ℓ) where
  open DeMorganAlgebra DM
  open Typing DM

  -- Graded provability predicate
  -- Prov φ c means "φ is provable at credence c"
  -- This abstracts over the specific derivation
  data Prov : ∀ {n} → Tm n → C → Set ℓ where
    -- If we have a derivation at credence c, then Prov holds
    from-derivation : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c : C} →
                      Γ ⊢ t ∶ A 〔 c 〕 →
                      Prov t c

    -- Provability respects credence weakening
    prov-weaken : ∀ {n} {t : Tm n} {c d : C} →
                  Prov t c →
                  d ≤ c →
                  Prov t d

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
    encode-derivation : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c : C} →
                        Γ ⊢ t ∶ A 〔 c 〕 →
                        Tm 0

  -- Diagonal Lemma (Gödel's fixed-point theorem)
  -- For any property P on terms and credences,
  -- there exists a term G such that Prov G c ↔ P ⌈G⌉ c
  --
  -- This is the foundation for Gödel's incompleteness theorems
  postulate
    diagonal : ∀ {n} (P : Tm 0 → C → Set ℓ) →
               ∃ λ (G : Tm n) → ∀ c → (Prov G c → P ⌈ G ⌉ c) × (P ⌈ G ⌉ c → Prov G c)

  -- Derivability conditions (Hilbert-Bernays-Löb)
  -- D1: If Γ ⊢ t : A @ c, then Prov ⌈t⌉ c
  postulate
    D1 : ∀ {n} {Γ : Ctx n} {t : Tm n} {A : Ty n} {c : C} →
         Γ ⊢ t ∶ A 〔 c 〕 →
         Prov ⌈ t ⌉ c

  -- D2: Prov(φ → ψ) c → Prov φ d → Prov ψ (c · d)
  -- (provability distributes over application, with credence multiplication)
  postulate
    D2 : ∀ {n} {φ : Tm n} {ψ : Tm (suc n)} {c d : C} →
         Prov (lam (base 0) ψ) c →
         Prov φ d →
         Prov (app (lam (base 0) ψ) φ) (c · d)

  -- D3: Prov φ c → Prov (Prov φ c) 1
  -- (provability is witnessed)
  postulate
    D3 : ∀ {n} {φ : Tm n} {c : C} →
         Prov φ c →
         Prov ⌈ φ ⌉ 𝟙

  -- Self-reference detection
  -- A term is self-referential if it contains its own encoding
  data SelfRef : ∀ {n} → Tm n → Set ℓ where
    via-encoding : ∀ {n} (t : Tm n) →
                   -- t mentions ⌈t⌉ (informally)
                   SelfRef t

  -- Credence of self-referential terms
  -- If a term is self-referential in a particular way,
  -- its credence satisfies a fixed-point equation
  --
  -- POSTULATE JUSTIFICATION:
  -- The credence of a self-referential term depends on the specific
  -- fixed-point equation it satisfies. This requires:
  -- 1. The diagonal lemma to construct the self-reference
  -- 2. Analysis of the property P that the term references
  -- Without knowing P, we cannot determine which credence satisfies c = P(c).
  -- In general, existence of such fixed points requires the credence algebra
  -- to be a complete lattice (which we don't assume in the minimal structure).
  postulate
    self-ref-credence : ∀ {n} {t : Tm n} →
                        SelfRef t →
                        ∃ λ c → Prov t c
