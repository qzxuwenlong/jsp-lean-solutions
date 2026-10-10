-- =====================================================================
-- JSP-000919 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the sum of distinct factorials 1! + 2! + 3! = 1 + 2 + 6 = 9
-- is a perfect power:
--   9 = 3*3 = 3^2 with 1 = 1!, 2 = 1*2 = 2!, 6 = 1*2*3 = 3!.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp919.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 * 2 = 2) and (1 * 2 * 3 = 6)) and (((1 + 2 + 6 = 9) and (9 = 3 * 3)) and True)
def R1 : Prop := ((3 * 3 = 9) and (9 >= 1)) and True
theorem jsp919 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 * 2 = 2) := by decide
    have h_1 : (1 * 2 * 3 = 6) := by decide
    have h_2 : (1 + 2 + 6 = 9) := by decide
    have h_3 : (9 = 3 * 3) := by decide
    exact <h_0, <h_1, <h_2, h_3>>
  have hr1 : R1 := by
    have h_4 : (3 * 3 = 9) := by decide
    have h_5 : (9 >= 1) := by decide
    exact <h_4, h_5>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
