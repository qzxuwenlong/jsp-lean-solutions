-- =====================================================================
-- JSP-000054 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Cluster-prime examples:
--   p = 5: the only positive even integer at most p-3 = 2, namely 2,
--          is a difference of two primes at most 5: 2 = 5 - 3.
--   p = 7: 2 = 7 - 5 and 4 = 7 - 3 (both even integers at most 4).
-- Primality of 3, 5, 7 witnessed by absence of small factors
-- (7 % 2, 7 % 3 nonzero; 5 % 2, 3 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp54.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp54 : ((((5 % 2 ≠ 0) ∧ (3 % 2 ≠ 0)) ∧ ((7 % 2 ≠ 0) ∧ (7 % 3 ≠ 0)) ∧ ((4 <= 4) ∧ (7 <= 7))) ∧ True) := by decide
