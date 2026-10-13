-- =====================================================================
-- JSP-000772 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the product of the consecutive intervals [1,4] and [6,6]
--   (1 * 2 * 3 * 4) * 6 = 144 = 12^2
-- is a perfect power.  The interval [1,4] is consecutive (1 <= 2, 2 <= 3,
-- 3 <= 4) and [6,6] is a single point.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp772.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp772 : ((((1 * 2 * 3 * 4 * 6 = 144) ∧ (144 = 12 * 12)) ∧ ((12 >= 1) ∧ (6 >= 1))) ∧ True) := by decide
