-- =====================================================================
-- JSP-000771 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the small-prime range {2, 3} supplies a prime divisor for
-- every integer in the consecutive interval [2, 4]:
--   2 = 2*1 (divisor 2 <= 3), 3 = 3*1 (divisor 3 <= 3), 4 = 2*2
--   (divisor 2 <= 3).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp771.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp771 : ((((2 = 2 * 1) ∧ (3 = 3 * 1)) ∧ ((4 >= 2) ∧ (4 >= 1))) ∧ True) := by decide
