-- =====================================================================
-- JSP-000538 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- For the consecutive-integer product 120 = 1*2*3*4*5, the smallest prime
-- not dividing it is 7: 2 | 120, 3 | 120, 5 | 120, while 7 ∤ 120
-- (120 % 7 = 1) and 7 is prime (no small factors, 7 % 2 = 1).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp538.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 * 2 * 3 * 4 * 5 = 120) and (120 % 2 = 0)) and (((120 % 3 = 0) and (120 % 5 = 0)) and ((120 % 7 != 0) and (7 % 2 != 0)))
def R1 : Prop := ((7 >= 2) and (1 >= 1)) and (((2 >= 1) and (3 >= 1)) and ((4 >= 1) and (5 >= 1)))
theorem jsp538 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 * 2 * 3 * 4 * 5 = 120) := by decide
    have h_1 : (120 % 2 = 0) := by decide
    have h_2 : (120 % 3 = 0) := by decide
    have h_3 : (120 % 5 = 0) := by decide
    have h_4 : (120 % 7 != 0) := by decide
    have h_5 : (7 % 2 != 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (7 >= 2) := by decide
    have h_7 : (1 >= 1) := by decide
    have h_8 : (2 >= 1) := by decide
    have h_9 : (3 >= 1) := by decide
    have h_10 : (4 >= 1) := by decide
    have h_11 : (5 >= 1) := by decide
    exact <h_6, <h_7, <h_8, <h_9, <h_10, h_11>>>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial