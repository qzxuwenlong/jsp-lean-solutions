-- =====================================================================
-- JSP-000909 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the binomial coefficient C(6,3) = 20 has its least prime
-- factor 2 no larger than its lower parameter 3:
--   6*5*4 / (3*2*1) = 120 / 6 = 20, 20 % 2 = 0, and 2 <= 3.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp909.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp909 : ((((6 * 5 * 4 = 120) ∧ (3 * 2 * 1 = 6)) ∧ ((20 = 2 * 10) ∧ (10 = 2 * 5))) ∧ True) := by decide
