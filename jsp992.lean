-- =====================================================================
-- JSP-000992 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: coloring positive integers by parity, the primes 3, 5, 7 form
-- a monochromatic (all odd) arithmetic progression:
--   5 - 3 = 2, 7 - 5 = 2, and 3, 5, 7 are all odd (3 % 2, 5 % 2, 7 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp992.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((5 - 3 = 2) and (7 - 5 = 2)) and (((3 % 2 != 0) and (5 % 2 != 0)) and ((7 % 2 != 0) and True))
def R1 : Prop := ((3 >= 1) and (7 >= 1)) and True
theorem jsp992 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (5 - 3 = 2) := by decide
    have h_1 : (7 - 5 = 2) := by decide
    have h_2 : (3 % 2 != 0) := by decide
    have h_3 : (5 % 2 != 0) := by decide
    have h_4 : (7 % 2 != 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, h_4>>
  have hr1 : R1 := by
    have h_5 : (3 >= 1) := by decide
    have h_6 : (7 >= 1) := by decide
    exact <h_5, h_6>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
