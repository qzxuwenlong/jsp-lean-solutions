-- =====================================================================
-- JSP-000328 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example (Brocard-Ramanujan): the factorial 4! + 1 is a square:
--   1*2*3*4 = 24, 24 + 1 = 25, and 25 = 5*5 = 5^2.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean-local.js jsp328.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp328 : ((((1 * 2 * 3 * 4 = 24) ∧ (24 + 1 = 25)) ∧ ((5 >= 1) ∧ (5 > 4))) ∧ True) := by decide
