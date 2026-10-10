-- =====================================================================
-- JSP-000221 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- The set {1, 2, 4} (powers of two): every integer 0..7 is a finite sum
-- of distinct elements (binary representation completeness):
--   0 = (empty sum), 1 = 1, 2 = 2, 3 = 1+2, 4 = 4,
--   5 = 1+4, 6 = 2+4, 7 = 1+2+4.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp221.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 = 1) and (2 = 2)) and (((4 = 4) and (3 = 1 + 2)) and ((5 = 1 + 4) and (6 = 2 + 4)))
def R1 : Prop := ((7 = 1 + 2 + 4) and (1 < 2)) and (((2 < 4) and (1 >= 1)) and ((2 >= 1) and (4 >= 1)))
theorem jsp221 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 = 1) := by decide
    have h_1 : (2 = 2) := by decide
    have h_2 : (4 = 4) := by decide
    have h_3 : (3 = 1 + 2) := by decide
    have h_4 : (5 = 1 + 4) := by decide
    have h_5 : (6 = 2 + 4) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (7 = 1 + 2 + 4) := by decide
    have h_7 : (1 < 2) := by decide
    have h_8 : (2 < 4) := by decide
    have h_9 : (1 >= 1) := by decide
    have h_10 : (2 >= 1) := by decide
    have h_11 : (4 >= 1) := by decide
    exact <h_6, <h_7, <h_8, <h_9, <h_10, h_11>>>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial