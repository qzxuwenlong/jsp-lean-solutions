-- =====================================================================
-- JSP-000051 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- The set {5, 7, 11}: no element divides the sum of the two larger ones
--   (5+7)%11 != 0, (5+11)%7 != 0, (7+11)%5 != 0.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp51.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((5 < 7) and (7 < 11)) and (((5 + 7 = 12) and (5 + 11 = 16)) and ((7 + 11 = 18) and (18 % 5 != 0)))
def R1 : Prop := ((16 % 7 != 0) and (12 % 11 != 0)) and (((5 >= 1) and (7 >= 1)) and ((11 >= 1) and True))
theorem jsp51 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (5 < 7) := by decide
    have h_1 : (7 < 11) := by decide
    have h_2 : (5 + 7 = 12) := by decide
    have h_3 : (5 + 11 = 16) := by decide
    have h_4 : (7 + 11 = 18) := by decide
    have h_5 : (18 % 5 != 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (16 % 7 != 0) := by decide
    have h_7 : (12 % 11 != 0) := by decide
    have h_8 : (5 >= 1) := by decide
    have h_9 : (7 >= 1) := by decide
    have h_10 : (11 >= 1) := by decide
    exact <h_6, <h_7, <h_8, <h_9, h_10>>>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial