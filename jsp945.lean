-- =====================================================================
-- JSP-000945 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 13 has the property that its differences from twice every
-- permitted smaller square are all prime:
--   13 - 2*1 = 11 (prime: 11 % 2, 11 % 3 nonzero) and
--   13 - 2*4 = 5  (prime: 5 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp945.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 * 1 = 2) and (13 - 2 = 11)) and (((11 % 2 != 0) and (11 % 3 != 0)) and ((2 * 4 = 8) and (13 - 8 = 5)))
def R1 : Prop := ((5 % 2 != 0) and (5 % 3 != 0)) and True
theorem jsp945 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (2 * 1 = 2) := by decide
    have h_1 : (13 - 2 = 11) := by decide
    have h_2 : (11 % 2 != 0) := by decide
    have h_3 : (11 % 3 != 0) := by decide
    have h_4 : (2 * 4 = 8) := by decide
    have h_5 : (13 - 8 = 5) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (5 % 2 != 0) := by decide
    have h_7 : (5 % 3 != 0) := by decide
    exact <h_6, h_7>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
