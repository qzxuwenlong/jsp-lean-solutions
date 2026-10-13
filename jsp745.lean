-- =====================================================================
-- JSP-000745 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example for coloring the integers so that no same-colored pair has
-- difference in a prescribed sparse set: take the parity coloring
--   col n := (n % 2 = 0)
-- and the sparse difference set {1}.  Within [1, 4], every pair at
-- distance 1 has distinct colors:
--   col 1 != col 2,  col 2 != col 3,  col 3 != col 4.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp745.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp745 : (((((1 % 2 ≠ 2 % 2) ∧ (2 % 2 ≠ 3 % 2)) ∧ (3 % 2 ≠ 4 % 2))) ∧ True) := by decide
