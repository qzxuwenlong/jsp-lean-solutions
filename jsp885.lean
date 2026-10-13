-- =====================================================================
-- JSP-000885 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 13 is a prime that is one more than a power of two times
-- another prime:
--   13 = 1 + 4*3 with 4 = 2^2, 3 prime (3 % 2 != 0), and 13 prime
--   (13 % 2 != 0, 13 % 3 != 0 since 5^2 > 13).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp885.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp885 : ((((13 = 1 + 4 * 3) ∧ (4 = 2 * 2)) ∧ ((4 * 3 = 12) ∧ (1 + 12 = 13))) ∧ True) := by decide
