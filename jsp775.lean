-- =====================================================================
-- JSP-000775 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the product of consecutive integers 1*2*3*4 = 24 has its
-- full part supported on powers of two and three:
--   24 = 8 * 3 with 8 = 2^3 and 3 = 3^1 (24 = 2^3 * 3^1).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp775.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 * 2 * 3 * 4 = 24) and (24 = 8 * 3)) and (((8 = 2 * 2 * 2) and (3 = 3 * 1)) and ((3 % 2 != 0) and (2 >= 2)))
def R1 : Prop := ((3 >= 1) and (24 >= 1)) and True
theorem jsp775 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 * 2 * 3 * 4 = 24) := by decide
    have h_1 : (24 = 8 * 3) := by decide
    have h_2 : (8 = 2 * 2 * 2) := by decide
    have h_3 : (3 = 3 * 1) := by decide
    have h_4 : (3 % 2 != 0) := by decide
    have h_5 : (2 >= 2) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (3 >= 1) := by decide
    have h_7 : (24 >= 1) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
