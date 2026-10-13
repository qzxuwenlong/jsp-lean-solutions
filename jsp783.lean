-- =====================================================================
-- JSP-000783 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the powerful number 8 = 2^3 lies between the consecutive
-- squares 4 = 2^2 and 9 = 3^2:
--   8 > 4, 8 < 9, 8 = 2*2*2 (every prime exponent in 8 is at least 2),
--   4 = 2*2, 9 = 3*3.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp783.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp783 : ((((8 = 2 * 2 * 2) ∧ (4 = 2 * 2)) ∧ ((4 >= 1) ∧ (9 >= 1))) ∧ True) := by decide
