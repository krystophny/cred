-- CredTT: A Type Theory with Primitive Credences
-- Complete module listing for typechecking all definitions

module CredTT.Everything where

-- Core modules (foundational, no dependencies except standard library)
import CredTT.Syntax
import CredTT.Substitution
import CredTT.Credence
import CredTT.Context

-- Neighbourhood semantics (stability definitions)
import CredTT.Neighbourhood
import CredTT.StabilityTheorems
import CredTT.Collapse

-- Typing judgment (depends on core)
import CredTT.Judgment

-- Properties of the type system (depends on judgment)
import CredTT.Properties

-- Provability predicates (depends on judgment)
import CredTT.Provability

-- MLTT embedding: {0,1} case (depends on judgment, credence)
import CredTT.MLTT

-- Examples using the type system
import CredTT.Examples

-- Proof techniques (all 28 with concrete examples)
import CredTT.ProofTechniques

-- Meta-theoretic results (depend on provability)
import CredTT.Incompleteness
import CredTT.Consistency
import CredTT.GradedChoice
import CredTT.Completeness

-- Self-hosting and reflection
import CredTT.Reflection
