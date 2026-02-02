-- Metatheory of CredTT: Subject Reduction and Progress
--
-- This module re-exports theorem STATEMENTS from CredTT.Metatheory.Statements.
--
-- IMPORTANT: These are STATEMENTS with postulates, NOT proofs!
-- The actual proofs are tracked in GitHub issues:
--   - Issue #186: Subject reduction (type preservation)
--   - Issue #187: Progress theorem
--
-- The statements establish the formal signatures of the theorems.
-- Proving them requires additional lemmas (canonical forms, inversion).

module CredTT.Metatheory where

-- Re-export all statement modules
open import CredTT.Metatheory.Statements public
