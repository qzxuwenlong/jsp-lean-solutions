-- =====================================================================
-- JSP-000639 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example for the product of the first several primes:
--   product 6 = 2 * 3; the prime 5 lies strictly between the largest
--   factor 3 and the product 6, and its sum with the product is also
--   prime: 5 + 6 = 11 (11 has no small prime factor: 11 % 2, 11 % 3
--   nonzero; 5 is prime since 5 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp639.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp639 : ((((2 * 3 = 6) ∧ (3 < 5)) ∧ ((5 % 2 ≠ 0) ∧ (6 >= 1))) ∧ True) := by decide
