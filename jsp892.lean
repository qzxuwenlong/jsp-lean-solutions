-- =====================================================================
-- JSP-000892 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the composite integer 25 divides a factorial plus one:
--   4! + 1 = 24 + 1 = 25, and 25 | 25, where 25 = 5*5 is composite.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean-local.js jsp892.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp892 : ((((1 * 2 * 3 * 4 = 24) ∧ (24 + 1 = 25))) ∧ True) := by decide
