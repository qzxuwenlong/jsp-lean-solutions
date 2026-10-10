-- =====================================================================
-- JSP-000783 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the powerful number 8 = 2^3 lies between the consecutive
-- squares 4 = 2^2 and 9 = 3^2:
--   8 > 4, 8 < 9, 8 = 2*2*2 (every prime exponent in 8 is at least 2),
--   4 = 2*2, 9 = 3*3.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp783.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((8 = 2 * 2 * 2) and (4 = 2 * 2)) and (((9 = 3 * 3) and (8 > 4)) and ((8 < 9) and (8 >= 1)))
def R1 : Prop := ((4 >= 1) and (9 >= 1)) and True
theorem jsp783 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (8 = 2 * 2 * 2) := by decide
    have h_1 : (4 = 2 * 2) := by decide
    have h_2 : (9 = 3 * 3) := by decide
    have h_3 : (8 > 4) := by decide
    have h_4 : (8 < 9) := by decide
    have h_5 : (8 >= 1) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (4 >= 1) := by decide
    have h_7 : (9 >= 1) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
