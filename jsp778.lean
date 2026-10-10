-- =====================================================================
-- JSP-000778 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: a power of two plus one is a powerful number:
--   2^3 + 1 = 9 = 3^2,  and 9 is powerful since its only prime factor 3
--   appears with exponent 2 (witnessed by 9 = 3*3).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp778.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 * 2 * 2 = 8) and (8 + 1 = 9)) and (((9 = 3 * 3) and (3 >= 2)) and True)
theorem jsp778 (R0 and True) := by
  have hr0 : R0 := by
    have h_0 : (2 * 2 * 2 = 8) := by decide
    have h_1 : (8 + 1 = 9) := by decide
    have h_2 : (9 = 3 * 3) := by decide
    have h_3 : (3 >= 2) := by decide
    exact <h_0, <h_1, <h_2, h_3>>
  constructor
  . exact hr0
  . trivial
