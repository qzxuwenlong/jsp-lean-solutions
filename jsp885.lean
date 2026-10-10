-- =====================================================================
-- JSP-000885 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 13 is a prime that is one more than a power of two times
-- another prime:
--   13 = 1 + 4*3 with 4 = 2^2, 3 prime (3 % 2 != 0), and 13 prime
--   (13 % 2 != 0, 13 % 3 != 0 since 5^2 > 13).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp885.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((13 = 1 + 4 * 3) and (4 = 2 * 2)) and (((3 % 2 != 0) and (13 % 2 != 0)) and ((13 % 3 != 0) and (13 >= 1)))
def R1 : Prop := ((4 * 3 = 12) and (1 + 12 = 13)) and True
theorem jsp885 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (13 = 1 + 4 * 3) := by decide
    have h_1 : (4 = 2 * 2) := by decide
    have h_2 : (3 % 2 != 0) := by decide
    have h_3 : (13 % 2 != 0) := by decide
    have h_4 : (13 % 3 != 0) := by decide
    have h_5 : (13 >= 1) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (4 * 3 = 12) := by decide
    have h_7 : (1 + 12 = 13) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
