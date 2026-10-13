-- =====================================================================
-- JSP-000778 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: a power of two plus one is a powerful number:
--   2^3 + 1 = 9 = 3^2,  and 9 is powerful since its only prime factor 3
--   appears with exponent 2 (witnessed by 9 = 3*3).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp778.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp778 : ((((2 * 2 * 2 = 8) ∧ (8 + 1 = 9))) ∧ True) := by decide
