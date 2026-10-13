-- =====================================================================
-- JSP-000873 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 6 is a multiply perfect number: the sum of its positive
-- divisors equals twice the number,
--   1 + 2 + 3 + 6 = 12 = 2 * 6.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean-local.js jsp873.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp873 : ((((1 + 2 + 3 + 6 = 12) ∧ (12 = 2 * 6))) ∧ True) := by decide
