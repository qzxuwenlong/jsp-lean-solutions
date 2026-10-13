-- =====================================================================
-- JSP-000945 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 13 has the property that its differences from twice every
-- permitted smaller square are all prime:
--   13 - 2*1 = 11 (prime: 11 % 2, 11 % 3 nonzero) and
--   13 - 2*4 = 5  (prime: 5 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp945.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp945 : (((((2 * 1 = 2) ∧ (13 - 2 * 1 = 11 ∧ (11 % 2 ≠ 0 ∧ 11 % 3 ≠ 0))) ∧ ((2 * 4 = 8) ∧ (13 - 2 * 4 = 5 ∧ (5 % 2 ≠ 0 ∧ 5 % 3 ≠ 0))))) ∧ True) := by decide
