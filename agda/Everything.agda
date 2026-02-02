module Everything where

-- CredTT: Type Theory with Primitive Credences
-- Credences from a De Morgan Algebra

-- Credence algebra (De Morgan, not semiring)
open import CredTT.Credence

-- Syntax: well-scoped terms and types
open import CredTT.Syntax

-- Substitution: parallel substitution with lift/weaken
open import CredTT.Substitution

-- Contexts: well-scoped typing contexts
open import CredTT.Context

-- Judgments: credence-weighted typing rules
open import CredTT.Judgment

-- Properties: metatheorems
open import CredTT.Properties

-- Decidability: type checking is decidable
-- open import CredTT.Decidability

-- Normalization: weak normalization via logical relations
-- open import CredTT.Normalization

-- MLTT: the {0,1} limiting case
open import CredTT.MLTT

-- Examples: identity, composition, ex falso
open import CredTT.Examples

-- Provability: graded provability predicates for meta-theory
open import CredTT.Provability

-- Incompleteness: Godel's theorems with graded credences
-- Key result: G has credence 1/2 (fixed point of negation)
open import CredTT.Incompleteness

-- Consistency: self-consistency at credence < 1
-- CredTT can prove its own consistency at graded credence
open import CredTT.Consistency

-- GradedChoice: Axiom of Choice at graded credences
-- Finite choice at 1, countable/uncountable at < 1
open import CredTT.GradedChoice

-- DependentCredences: credences that vary over the domain
-- (x : A) -> B @ c(x) where c depends on x
open import CredTT.DependentCredences
