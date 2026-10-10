-- =====================================================================
-- JSP-000049 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Five integers represented as a power of 2 plus one prime:
--   9  = 2^2 + 5,  13 = 2^3 + 5,  17 = 2^2 + 13,
--   21 = 2^2 + 17, 29 = 2^4 + 13.
-- Primality witnessed by absence of small factors (d^2 <= p check).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp49.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 * 2 = 4) and (2 * 2 * 2 = 8)) and (((2 * 2 * 2 * 2 = 16) and (5 % 2 != 0)) and ((13 % 2 != 0) and (13 % 3 != 0)))
def R1 : Prop := ((17 % 2 != 0) and (17 % 3 != 0)) and (((29 % 2 != 0) and (29 % 3 != 0)) and ((29 % 5 != 0) and (4 + 5 = 9)))
def R2 : Prop := ((8 + 5 = 13) and (4 + 13 = 17)) and (((4 + 17 = 21) and (16 + 13 = 29)) and (((9 >= 9) and (13 >= 9)) and ((17 >= 9) and (21 >= 9))))
def R3 : Prop := ((29 >= 9) and (5 >= 2)) and (((13 >= 2) and (17 >= 2)) and ((29 >= 2) and True))
theorem jsp49 (R0 and (R1 and (R2 and (R3 and True)))) := by
  have hr0 : R0 := by
    have h_0 : (2 * 2 = 4) := by decide
    have h_1 : (2 * 2 * 2 = 8) := by decide
    have h_2 : (2 * 2 * 2 * 2 = 16) := by decide
    have h_3 : (5 % 2 != 0) := by decide
    have h_4 : (13 % 2 != 0) := by decide
    have h_5 : (13 % 3 != 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (17 % 2 != 0) := by decide
    have h_7 : (17 % 3 != 0) := by decide
    have h_8 : (29 % 2 != 0) := by decide
    have h_9 : (29 % 3 != 0) := by decide
    have h_10 : (29 % 5 != 0) := by decide
    have h_11 : (4 + 5 = 9) := by decide
    exact <h_6, <h_7, <h_8, <h_9, <h_10, h_11>>>>
  have hr2 : R2 := by
    have h_12 : (8 + 5 = 13) := by decide
    have h_13 : (4 + 13 = 17) := by decide
    have h_14 : (4 + 17 = 21) := by decide
    have h_15 : (16 + 13 = 29) := by decide
    have h_16 : (9 >= 9) := by decide
    have h_17 : (13 >= 9) := by decide
    have h_18 : (17 >= 9) := by decide
    have h_19 : (21 >= 9) := by decide
    exact <h_12, <h_13, <h_14, <h_15, <h_16, <h_17, <h_18, h_19>>>>
  have hr3 : R3 := by
    have h_20 : (29 >= 9) := by decide
    have h_21 : (5 >= 2) := by decide
    have h_22 : (13 >= 2) := by decide
    have h_23 : (17 >= 2) := by decide
    have h_24 : (29 >= 2) := by decide
    exact <h_20, <h_21, <h_22, <h_23, h_24>>>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . constructor
  . exact hr2
  . constructor
  . exact hr3
  . trivial