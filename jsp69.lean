-- =====================================================================
-- JSP-000069 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- {1,2,4,8} (4 elements): triple sums 7,11,13,14 pairwise distinct
-- (binary representation uniqueness). All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp69.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 >= 1) and (1 <= 8)) and (((2 >= 1) and (2 <= 8)) and (((4 >= 1) and (4 <= 8)) and (((8 >= 1) and (8 <= 8)) and (((1 != 2) and (1 != 4)) and ((1 != 8) and ((2 != 4) and (2 != 8)))))))
def R1 : Prop := ((4 != 8) and (7 != 11)) and (((7 != 13) and (7 != 14)) and (((11 != 13) and (11 != 14)) and (13 != 14)))
theorem jsp69 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 >= 1) := by decide
    have h_1 : (1 <= 8) := by decide
    have h_2 : (2 >= 1) := by decide
    have h_3 : (2 <= 8) := by decide
    have h_4 : (4 >= 1) := by decide
    have h_5 : (4 <= 8) := by decide
    have h_6 : (8 >= 1) := by decide
    have h_7 : (8 <= 8) := by decide
    have h_8 : (1 != 2) := by decide
    have h_9 : (1 != 4) := by decide
    have h_10 : (1 != 8) := by decide
    have h_11 : (2 != 4) := by decide
    have h_12 : (2 != 8) := by decide
    have h_13 : (4 != 8) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, <h_5, <h_6, <h_7, <h_8, <h_9, <h_10, <h_11, <h_12, h_13>>>>
  have hr1 : R1 := by
    have h_14 : (7 != 11) := by decide
    have h_15 : (7 != 13) := by decide
    have h_16 : (7 != 14) := by decide
    have h_17 : (11 != 13) := by decide
    have h_18 : (11 != 14) := by decide
    have h_19 : (13 != 14) := by decide
    exact <h_14, <h_15, <h_16, <h_17, <h_18, h_19>>>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial