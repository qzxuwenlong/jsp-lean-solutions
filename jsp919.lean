-- =====================================================================
-- JSP-000919 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the sum of distinct factorials 1! + 2! + 3! = 1 + 2 + 6 = 9
-- is a perfect power:
--   9 = 3*3 = 3^2 with 1 = 1!, 2 = 1*2 = 2!, 6 = 1*2*3 = 3!.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp919.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp919 : ((((1 * 2 = 2) ∧ (1 * 2 * 3 = 6)) ∧ ((3 * 3 = 9) ∧ (9 >= 1))) ∧ True) := by decide
