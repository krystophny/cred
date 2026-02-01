module Everything where

-- ProbTT: Type Theory with Primitive Weights
-- Weights from a De Morgan Algebra

-- Weight algebra (De Morgan, not semiring)
open import ProbTT.Weight

-- Syntax: well-scoped terms and types
open import ProbTT.Syntax

-- Substitution: parallel substitution with lift/weaken
open import ProbTT.Substitution

-- Contexts: well-scoped typing contexts
open import ProbTT.Context

-- Judgments: weighted typing rules
open import ProbTT.Judgment

-- Properties: metatheorems
open import ProbTT.Properties

-- MLTT: the {0,1} limiting case
open import ProbTT.MLTT

-- Examples: identity, composition, ex falso
open import ProbTT.Examples
