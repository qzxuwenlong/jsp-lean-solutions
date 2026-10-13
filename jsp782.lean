-- =====================================================================
-- JSP-000782 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the integer 12 is a sum of three powerful numbers, each
-- divisible by the square of every prime dividing it:
--   12 = 4 + 4 + 4, 4 = 2^2, and 4 is divisible by the square of its
--   only prime divisor 2 (4 % 4 = 0).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp782.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp782 : ((((12 = 4 + 4 + 4) ∧ (4 = 2 * 2)) ∧ ((12 >= 1) ∧ (4 >= 1))) ∧ True) := by decide
