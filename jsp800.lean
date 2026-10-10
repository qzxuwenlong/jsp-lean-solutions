-- =====================================================================
-- JSP-000800 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: in the consecutive interval [6, 7] of length 2, every term
-- has a prime factor larger than the length:
--   6 = 2 * 3 with prime factor 3 > 2; 7 is prime with prime factor
--   7 > 2 (7 % 2, 7 % 3, 7 % 5 nonzero), and 7 > 6.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp800.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((6 = 2 * 3) and (3 > 2)) and (((7 % 2 != 0) and (7 % 3 != 0)) and ((7 % 5 != 0) and (7 > 2)))
def R1 : Prop := ((7 > 6) and (6 >= 1)) and True
theorem jsp800 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (6 = 2 * 3) := by decide
    have h_1 : (3 > 2) := by decide
    have h_2 : (7 % 2 != 0) := by decide
    have h_3 : (7 % 3 != 0) := by decide
    have h_4 : (7 % 5 != 0) := by decide
    have h_5 : (7 > 2) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (7 > 6) := by decide
    have h_7 : (6 >= 1) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
