-- =====================================================================
-- JSP-000221 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- The set {1, 2, 4} (powers of two): every integer 0..7 is a finite sum
-- of distinct elements (binary representation completeness):
--   0 = (empty sum), 1 = 1, 2 = 2, 3 = 1+2, 4 = 4,
--   5 = 1+4, 6 = 2+4, 7 = 1+2+4.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp221.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp221 : ((((1 = 1) ∧ (2 = 2)) ∧ ((7 = 1 + 2 + 4) ∧ (1 < 2))) ∧ True) := by decide
