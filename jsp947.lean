-- =====================================================================
-- JSP-000947 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 7 has the property that its differences from every permitted
-- smaller power of two are all prime:
--   7 - 2 = 5 (prime: 5 % 2, 5 % 3 nonzero) and
--   7 - 4 = 3 (prime: 3 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp947.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((7 - 2 = 5) and (5 % 2 != 0)) and (((5 % 3 != 0) and (7 - 4 = 3)) and ((3 % 2 != 0) and True))
def R1 : Prop := ((7 >= 1) and (7 > 4)) and True
theorem jsp947 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (7 - 2 = 5) := by decide
    have h_1 : (5 % 2 != 0) := by decide
    have h_2 : (5 % 3 != 0) := by decide
    have h_3 : (7 - 4 = 3) := by decide
    have h_4 : (3 % 2 != 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, h_4>>
  have hr1 : R1 := by
    have h_5 : (7 >= 1) := by decide
    have h_6 : (7 > 4) := by decide
    exact <h_5, h_6>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
