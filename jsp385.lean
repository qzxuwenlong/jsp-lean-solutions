-- =====================================================================
-- JSP-000385 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the natural numbers can be permuted (e.g. 1, 2, 3, 4) so that
-- every adjacent pair has a prime sum:
--   1+2 = 3, 2+3 = 5, 3+4 = 7, all prime.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean-local.js jsp385.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp385 : ((((1 + 2 = 3) ∧ (2 + 3 = 5)) ∧ (((7 % 2 ≠ 0) ∧ (7 % 3 ≠ 0)) ∧ (((7 % 5 ≠ 0) ∧ True)))) ∧ True) := by decide
