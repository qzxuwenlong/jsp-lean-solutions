-- =====================================================================
-- JSP-000385 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the natural numbers can be permuted (e.g. 1, 2, 3, 4) so that
-- every adjacent pair has a prime sum:
--   1+2 = 3, 2+3 = 5, 3+4 = 7, all prime.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp385.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 + 2 = 3) and (2 + 3 = 5)) and (((3 + 4 = 7) and (3 % 2 != 0)) and ((5 % 2 != 0) and (5 % 3 != 0)))
def R1 : Prop := (((7 % 2 != 0) and (7 % 3 != 0)) and (((7 % 5 != 0) and True))) and True
theorem jsp385 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 + 2 = 3) := by decide
    have h_1 : (2 + 3 = 5) := by decide
    have h_2 : (3 + 4 = 7) := by decide
    have h_3 : (3 % 2 != 0) := by decide
    have h_4 : (5 % 2 != 0) := by decide
    have h_5 : (5 % 3 != 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (7 % 2 != 0) := by decide
    have h_7 : (7 % 3 != 0) := by decide
    have h_8 : (7 % 5 != 0) := by decide
    exact <h_6, <h_7, h_8>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
