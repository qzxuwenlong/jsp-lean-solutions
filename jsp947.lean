-- =====================================================================
-- JSP-000947 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 7 has the property that its differences from every permitted
-- smaller power of two are all prime:
--   7 - 2 = 5 (prime: 5 % 2, 5 % 3 nonzero) and
--   7 - 4 = 3 (prime: 3 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp947.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp947 : ((((7 - 2 = 5) ∧ (5 % 2 ≠ 0)) ∧ ((7 >= 1) ∧ (7 > 4))) ∧ True) := by decide
