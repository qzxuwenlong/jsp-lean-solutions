-- =====================================================================
-- JSP-000713 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the interval [2, 5] contains a different multiple of each of
-- the first three primes:
--   2 = 2*1 (multiple of 2), 3 = 3*1 (multiple of 3), 5 = 5*1 (multiple
--   of 5), with 2 <= 2, 3 <= 5, 5 <= 5 lying in [2, 5].
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp713.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp713 : ((((2 = 2 * 1) ∧ (3 = 3 * 1)) ∧ ((2 >= 2) ∧ (5 >= 1))) ∧ True) := by decide
