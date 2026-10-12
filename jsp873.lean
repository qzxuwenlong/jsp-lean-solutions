-- =====================================================================
-- JSP-000873 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 6 is a multiply perfect number: the sum of its positive
-- divisors equals twice the number,
--   1 + 2 + 3 + 6 = 12 = 2 * 6.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp873.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 + 2 + 3 + 6 = 12) and (12 = 2 * 6)) and True
theorem jsp873 (R0 and True) := by
  have hr0 : R0 := by
    have h_0 : (1 + 2 + 3 + 6 = 12) := by decide
    have h_1 : (12 = 2 * 6) := by decide
    exact <h_0, h_1>
  constructor
  . exact hr0
  . trivial
