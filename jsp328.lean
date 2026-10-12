-- =====================================================================
-- JSP-000328 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example (Brocard-Ramanujan): the factorial 4! + 1 is a square:
--   1*2*3*4 = 24, 24 + 1 = 25, and 25 = 5*5 = 5^2.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp328.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 * 2 * 3 * 4 = 24) and (24 + 1 = 25)) and (((25 = 5 * 5) and (25 >= 1)) and True)
def R1 : Prop := ((5 >= 1) and (5 > 4)) and True
theorem jsp328 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 * 2 * 3 * 4 = 24) := by decide
    have h_1 : (24 + 1 = 25) := by decide
    have h_2 : (25 = 5 * 5) := by decide
    have h_3 : (25 >= 1) := by decide
    exact <h_0, <h_1, <h_2, h_3>>
  have hr1 : R1 := by
    have h_4 : (5 >= 1) := by decide
    have h_5 : (5 > 4) := by decide
    exact <h_4, h_5>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
