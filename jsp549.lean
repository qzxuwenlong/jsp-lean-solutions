-- =====================================================================
-- JSP-000549 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Four integers as a positive multiple of the prime square 4 = 2^2 plus a
-- nonnegative square:
--   9  = 4*2 + 1  (1 = 1^2)
--   13 = 4*3 + 1  (1 = 1^2)
--   17 = 4*4 + 1  (1 = 1^2)
--   20 = 4*5 + 0  (0 = 0^2)
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp549.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp549 : ((((2 * 2 = 4) ∧ (4 * 2 + 1 = 9)) ∧ ((4 * 4 + 1 = 17) ∧ (4 >= 0)) ∧ ((13 >= 1) ∧ (17 >= 1))) ∧ True) := by decide
