-- =====================================================================
-- JSP-000782 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the integer 12 is a sum of three powerful numbers, each
-- divisible by the square of every prime dividing it:
--   12 = 4 + 4 + 4, 4 = 2^2, and 4 is divisible by the square of its
--   only prime divisor 2 (4 % 4 = 0).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp782.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((12 = 4 + 4 + 4) and (4 = 2 * 2)) and (((4 % 4 = 0) and (2 % 2 = 0)) and True)
def R1 : Prop := ((12 >= 1) and (4 >= 1)) and True
theorem jsp782 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (12 = 4 + 4 + 4) := by decide
    have h_1 : (4 = 2 * 2) := by decide
    have h_2 : (4 % 4 = 0) := by decide
    have h_3 : (2 % 2 = 0) := by decide
    exact <h_0, <h_1, <h_2, h_3>>
  have hr1 : R1 := by
    have h_4 : (12 >= 1) := by decide
    have h_5 : (4 >= 1) := by decide
    exact <h_4, h_5>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
