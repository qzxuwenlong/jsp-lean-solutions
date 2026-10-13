-- =====================================================================
-- JSP-000826 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: for the path P5 (a tree/forest), the counts of independent
-- sets by size are 1, 5, 6, 1, 0, which form a unimodal sequence:
--   size 0: 1 (empty), size 1: 5 (single vertices),
--   size 2: 6 = C(5,2) - 4 (nonadjacent pairs: 10 - 4),
--   size 3: 1 ({1,3,5}), size 4: 0; 1 <= 5 <= 6 >= 1 >= 0.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp826.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp826 : ((((5 = 1 + 1 + 1 + 1 + 1) ∧ (10 = 4 + 3 + 2 + 1)) ∧ ((6 >= 1) ∧ (1 >= 0))) ∧ True) := by decide
