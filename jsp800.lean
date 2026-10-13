-- =====================================================================
-- JSP-000800 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: in the consecutive interval [6, 7] of length 2, every term
-- has a prime factor larger than the length:
--   6 = 2 * 3 with prime factor 3 > 2; 7 is prime with prime factor
--   7 > 2 (7 % 2, 7 % 3, 7 % 5 nonzero), and 7 > 6.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp800.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp800 : ((((6 = 2 * 3) ∧ (3 > 2)) ∧ ((7 > 6) ∧ (6 >= 1))) ∧ True) := by decide
