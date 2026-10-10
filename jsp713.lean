-- =====================================================================
-- JSP-000713 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the interval [2, 5] contains a different multiple of each of
-- the first three primes:
--   2 = 2*1 (multiple of 2), 3 = 3*1 (multiple of 3), 5 = 5*1 (multiple
--   of 5), with 2 <= 2, 3 <= 5, 5 <= 5 lying in [2, 5].
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp713.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 = 2 * 1) and (3 = 3 * 1)) and (((5 = 5 * 1) and (2 <= 2)) and ((3 <= 5) and (5 <= 5)))
def R1 : Prop := ((2 >= 2) and (5 >= 1)) and True
theorem jsp713 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (2 = 2 * 1) := by decide
    have h_1 : (3 = 3 * 1) := by decide
    have h_2 : (5 = 5 * 1) := by decide
    have h_3 : (2 <= 2) := by decide
    have h_4 : (3 <= 5) := by decide
    have h_5 : (5 <= 5) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (2 >= 2) := by decide
    have h_7 : (5 >= 1) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
