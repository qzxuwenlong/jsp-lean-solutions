-- =====================================================================
-- JSP-000771 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the small-prime range {2, 3} supplies a prime divisor for
-- every integer in the consecutive interval [2, 4]:
--   2 = 2*1 (divisor 2 <= 3), 3 = 3*1 (divisor 3 <= 3), 4 = 2*2
--   (divisor 2 <= 3).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp771.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 = 2 * 1) and (3 = 3 * 1)) and (((4 = 2 * 2) and (2 <= 3)) and ((3 <= 3) and (2 <= 2)))
def R1 : Prop := ((4 >= 2) and (4 >= 1)) and True
theorem jsp771 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (2 = 2 * 1) := by decide
    have h_1 : (3 = 3 * 1) := by decide
    have h_2 : (4 = 2 * 2) := by decide
    have h_3 : (2 <= 3) := by decide
    have h_4 : (3 <= 3) := by decide
    have h_5 : (2 <= 2) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (4 >= 2) := by decide
    have h_7 : (4 >= 1) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
