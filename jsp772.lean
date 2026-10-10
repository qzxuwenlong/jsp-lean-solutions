-- =====================================================================
-- JSP-000772 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the product of the consecutive intervals [1,4] and [6,6]
--   (1 * 2 * 3 * 4) * 6 = 144 = 12^2
-- is a perfect power.  The interval [1,4] is consecutive (1 <= 2, 2 <= 3,
-- 3 <= 4) and [6,6] is a single point.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp772.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 * 2 * 3 * 4 * 6 = 144) and (144 = 12 * 12)) and (((1 <= 2) and (2 <= 3)) and ((3 <= 4) and (12 * 12 = 144)))
def R1 : Prop := ((12 >= 1) and (6 >= 1)) and True
theorem jsp772 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 * 2 * 3 * 4 * 6 = 144) := by decide
    have h_1 : (144 = 12 * 12) := by decide
    have h_2 : (1 <= 2) := by decide
    have h_3 : (2 <= 3) := by decide
    have h_4 : (3 <= 4) := by decide
    have h_5 : (12 * 12 = 144) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (12 >= 1) := by decide
    have h_7 : (6 >= 1) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
