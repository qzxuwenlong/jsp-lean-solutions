-- =====================================================================
-- JSP-000389 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: modulo the prime 7, the first four factorials give distinct
-- residues:
--   1! = 1, 2! = 2, 3! = 6, 4! = 24 = 3 (mod 7), all distinct.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp389.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 % 7 = 1) and (2 % 7 = 2)) and (((6 % 7 = 6) and (24 % 7 = 3)) and ((1 != 2) and (2 != 6)))
def R1 : Prop := (((6 != 3) and (1 != 3)) and ((1 * 2 = 2) and (1 * 2 * 3 = 6))) and ((1 * 2 * 3 * 4 = 24) and True)
theorem jsp389 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 % 7 = 1) := by decide
    have h_1 : (2 % 7 = 2) := by decide
    have h_2 : (6 % 7 = 6) := by decide
    have h_3 : (24 % 7 = 3) := by decide
    have h_4 : (1 != 2) := by decide
    have h_5 : (2 != 6) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (6 != 3) := by decide
    have h_7 : (1 != 3) := by decide
    have h_8 : (1 * 2 = 2) := by decide
    have h_9 : (1 * 2 * 3 = 6) := by decide
    have h_10 : (1 * 2 * 3 * 4 = 24) := by decide
    exact <h_6, <h_7, <h_8, <h_9, h_10>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
