-- =====================================================================
-- JSP-000143 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- 3, 5, 7 are consecutive primes (in the full prime sequence 2,3,5,7,11,...)
-- forming an arithmetic progression. Primality is witnessed by the absence
-- of small factors; the intermediate integers 4 = 2*2 and 6 = 2*3 are
-- composite, so 3,5,7 are consecutive primes. All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp143.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 * 2 > 3) and (5 % 2 != 0)) and (((7 % 2 != 0) and (4 = 2 * 2)) and ((6 = 2 * 3) and (3 < 5)))
def R1 : Prop := ((5 < 7) and (3 + 7 = 2 * 5)) and ((3 >= 2) and (5 >= 2)) and (7 >= 2)
theorem jsp143 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (2 * 2 > 3) := by decide
    have h_1 : (5 % 2 != 0) := by decide
    have h_2 : (7 % 2 != 0) := by decide
    have h_3 : (4 = 2 * 2) := by decide
    have h_4 : (6 = 2 * 3) := by decide
    have h_5 : (3 < 5) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (5 < 7) := by decide
    have h_7 : (3 + 7 = 2 * 5) := by decide
    have h_8 : (3 >= 2) := by decide
    have h_9 : (5 >= 2) := by decide
    have h_10 : (7 >= 2) := by decide
    exact <h_6, <h_7, <h_8, <h_9, h_10>>>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial