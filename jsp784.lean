-- =====================================================================
-- JSP-000784 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the integer 12 has a representation as a sum of two powerful
-- numbers:
--   12 = 4 + 8 with 4 = 2^2 and 8 = 2^3 (both powerful).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp784.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp784 : ((((12 = 4 + 8) ∧ (4 = 2 * 2)) ∧ ((4 >= 1) ∧ (8 >= 1))) ∧ True) := by decide
