-- =====================================================================
-- JSP-000549 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Four integers as a positive multiple of the prime square 4 = 2^2 plus a
-- nonnegative square:
--   9  = 4*2 + 1  (1 = 1^2)
--   13 = 4*3 + 1  (1 = 1^2)
--   17 = 4*4 + 1  (1 = 1^2)
--   20 = 4*5 + 0  (0 = 0^2)
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp549.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 * 2 = 4) and (4 * 2 + 1 = 9)) and (((1 * 1 = 1) and (2 >= 0)) and ((4 * 3 + 1 = 13) and (3 >= 0)))
def R1 : Prop := ((4 * 4 + 1 = 17) and (4 >= 0)) and (((4 * 5 + 0 = 20) and (5 >= 0)) and ((0 * 0 = 0) and (9 >= 1)))
def R2 : Prop := ((13 >= 1) and (17 >= 1)) and ((20 >= 1) and True)
theorem jsp549 (R0 and (R1 and (R2 and True))) := by
  have hr0 : R0 := by
    have h_0 : (2 * 2 = 4) := by decide
    have h_1 : (4 * 2 + 1 = 9) := by decide
    have h_2 : (1 * 1 = 1) := by decide
    have h_3 : (2 >= 0) := by decide
    have h_4 : (4 * 3 + 1 = 13) := by decide
    have h_5 : (3 >= 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (4 * 4 + 1 = 17) := by decide
    have h_7 : (4 >= 0) := by decide
    have h_8 : (4 * 5 + 0 = 20) := by decide
    have h_9 : (5 >= 0) := by decide
    have h_10 : (0 * 0 = 0) := by decide
    have h_11 : (9 >= 1) := by decide
    exact <h_6, <h_7, <h_8, <h_9, <h_10, h_11>>>>
  have hr2 : R2 := by
    have h_12 : (13 >= 1) := by decide
    have h_13 : (17 >= 1) := by decide
    have h_14 : (20 >= 1) := by decide
    exact <h_12, <h_13, h_14>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . constructor
  . exact hr2
  . trivial
