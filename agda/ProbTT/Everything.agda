-- ProbTT: A Type Theory with Primitive Weights
-- Complete module listing for typechecking all definitions

module ProbTT.Everything where

-- Core modules (foundational, no dependencies except standard library)
import ProbTT.Syntax
import ProbTT.Substitution
import ProbTT.Weight
import ProbTT.Context

-- Typing judgment (depends on core)
import ProbTT.Judgment

-- Properties of the type system (depends on judgment)
import ProbTT.Properties

-- Provability predicates (depends on judgment)
import ProbTT.Provability

-- MLTT embedding: {0,1} case (depends on judgment, weight)
import ProbTT.MLTT

-- Examples using the type system
import ProbTT.Examples

-- Meta-theoretic results (depend on provability)
import ProbTT.Incompleteness
import ProbTT.Consistency
import ProbTT.GradedChoice
import ProbTT.Completeness
