-- =====================================================================
-- JSP-000639 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example for the product of the first several primes:
--   product 6 = 2 * 3; the prime 5 lies strictly between the largest
--   factor 3 and the product 6, and its sum with the product is also
--   prime: 5 + 6 = 11 (11 has no small prime factor: 11 % 2, 11 % 3
--   nonzero; 5 is prime since 5 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp639.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 * 3 = 6) and (3 < 5)) and (((5 < 6) and (5 + 6 = 11)) and ((11 % 2 != 0) and (11 % 3 != 0)))
def R1 : Prop := ((5 % 2 != 0) and (6 >= 1)) and True
theorem jsp639 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (2 * 3 = 6) := by decide
    have h_1 : (3 < 5) := by decide
    have h_2 : (5 < 6) := by decide
    have h_3 : (5 + 6 = 11) := by decide
    have h_4 : (11 % 2 != 0) := by decide
    have h_5 : (11 % 3 != 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (5 % 2 != 0) := by decide
    have h_7 : (6 >= 1) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
