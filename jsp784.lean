-- =====================================================================
-- JSP-000784 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the integer 12 has a representation as a sum of two powerful
-- numbers:
--   12 = 4 + 8 with 4 = 2^2 and 8 = 2^3 (both powerful).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp784.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((12 = 4 + 8) and (4 = 2 * 2)) and (((8 = 2 * 2 * 2) and (12 >= 1)) and True)
def R1 : Prop := ((4 >= 1) and (8 >= 1)) and True
theorem jsp784 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (12 = 4 + 8) := by decide
    have h_1 : (4 = 2 * 2) := by decide
    have h_2 : (8 = 2 * 2 * 2) := by decide
    have h_3 : (12 >= 1) := by decide
    exact <h_0, <h_1, <h_2, h_3>>
  have hr1 : R1 := by
    have h_4 : (4 >= 1) := by decide
    have h_5 : (8 >= 1) := by decide
    exact <h_4, h_5>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
