-- =====================================================================
-- JSP-000909 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the binomial coefficient C(6,3) = 20 has its least prime
-- factor 2 no larger than its lower parameter 3:
--   6*5*4 / (3*2*1) = 120 / 6 = 20, 20 % 2 = 0, and 2 <= 3.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp909.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((6 * 5 * 4 = 120) and (3 * 2 * 1 = 6)) and (((120 / 6 = 20) and (20 % 2 = 0)) and ((2 <= 3) and True))
def R1 : Prop := ((20 = 2 * 10) and (10 = 2 * 5)) and True
theorem jsp909 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (6 * 5 * 4 = 120) := by decide
    have h_1 : (3 * 2 * 1 = 6) := by decide
    have h_2 : (120 / 6 = 20) := by decide
    have h_3 : (20 % 2 = 0) := by decide
    have h_4 : (2 <= 3) := by decide
    exact <h_0, <h_1, <h_2, <h_3, h_4>>
  have hr1 : R1 := by
    have h_5 : (20 = 2 * 10) := by decide
    have h_6 : (10 = 2 * 5) := by decide
    exact <h_5, h_6>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
