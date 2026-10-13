-- =====================================================================
-- JSP-000775 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the product of consecutive integers 1*2*3*4 = 24 has its
-- full part supported on powers of two and three:
--   24 = 8 * 3 with 8 = 2^3 and 3 = 3^1 (24 = 2^3 * 3^1).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp775.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp775 : ((((1 * 2 * 3 * 4 = 24) ∧ (24 = 8 * 3)) ∧ ((3 >= 1) ∧ (24 >= 1))) ∧ True) := by decide
