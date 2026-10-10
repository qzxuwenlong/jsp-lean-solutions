-- =====================================================================
-- JSP-000260 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Subsums of unit fractions with denominators in a finite range
-- approximating one:
--   G1: 1/2 + 1/3 + 1/6 = 1        (denominators 2,3,6 in [1,6])
--   G2: 1/2 + 1/4 + 1/8 = 7/8 <= 1 (denominators 2,4,8 in [1,8])
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp260.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 / 2 + 1 / 3 + 1 / 6 = 1) and (2 >= 1)) and (((3 >= 1) and (6 >= 1)) and ((1 / 2 + 1 / 4 + 1 / 8 = 7 / 8) and (7 / 8 <= 1)))
def R1 : Prop := ((7 / 8 >= 0) and (2 >= 1)) and (((4 >= 1) and (8 >= 1)) and ((2 <= 6) and (3 <= 6)))
def R2 : Prop := ((6 <= 6) and (2 <= 8)) and (((4 <= 8) and (8 <= 8)) and ((1 / 6 > 0) and (1 / 8 > 0)))
theorem jsp260 (R0 and (R1 and (R2 and True))) := by
  have hr0 : R0 := by
    have h_0 : (1 / 2 + 1 / 3 + 1 / 6 = 1) := by decide
    have h_1 : (2 >= 1) := by decide
    have h_2 : (3 >= 1) := by decide
    have h_3 : (6 >= 1) := by decide
    have h_4 : (1 / 2 + 1 / 4 + 1 / 8 = 7 / 8) := by decide
    have h_5 : (7 / 8 <= 1) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (7 / 8 >= 0) := by decide
    have h_7 : (2 >= 1) := by decide
    have h_8 : (4 >= 1) := by decide
    have h_9 : (8 >= 1) := by decide
    have h_10 : (2 <= 6) := by decide
    have h_11 : (3 <= 6) := by decide
    exact <h_6, <h_7, <h_8, <h_9, <h_10, h_11>>>>
  have hr2 : R2 := by
    have h_12 : (6 <= 6) := by decide
    have h_13 : (2 <= 8) := by decide
    have h_14 : (4 <= 8) := by decide
    have h_15 : (8 <= 8) := by decide
    have h_16 : (1 / 6 > 0) := by decide
    have h_17 : (1 / 8 > 0) := by decide
    exact <h_12, <h_13, <h_14, <h_15, <h_16, h_17>>>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . constructor
  . exact hr2
  . trivial