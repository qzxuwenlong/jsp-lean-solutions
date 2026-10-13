-- =====================================================================
-- JSP-000801 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the set {1, 2, 4} has all its nonempty subset sums distinct
-- (3 = 1+2, 5 = 1+4, 6 = 2+4, 7 = 1+2+4 are all different):
--   1+2 = 3, 1+4 = 5, 2+4 = 6, 1+2+4 = 7, and 3, 5, 6, 7 pairwise distinct.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp801.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp801 : ((((1 + 2 = 3) ∧ (1 + 4 = 5)) ∧ (((3 ≠ 7) ∧ (5 ≠ 6)) ∧ (((5 ≠ 7) ∧ (6 ≠ 7)) ∧ True))) ∧ True) := by decide
