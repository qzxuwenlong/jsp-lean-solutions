-- =====================================================================
-- JSP-000986 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: for the logarithmically short consecutive interval [1, 2],
-- the product 1*2 = 2 is not divisible by 3, and 3 is the smallest
-- prime not dividing it (2 divides 2; 3 is prime with 3 > 2).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp986.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 * 2 = 2) and (2 % 2 = 0)) and (((2 % 3 != 0) and (3 % 2 != 0)) and ((3 > 2) and (3 >= 1)))
def R1 : Prop := ((2 >= 1) and (2 % 1 = 0)) and True
theorem jsp986 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 * 2 = 2) := by decide
    have h_1 : (2 % 2 = 0) := by decide
    have h_2 : (2 % 3 != 0) := by decide
    have h_3 : (3 % 2 != 0) := by decide
    have h_4 : (3 > 2) := by decide
    have h_5 : (3 >= 1) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (2 >= 1) := by decide
    have h_7 : (2 % 1 = 0) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
