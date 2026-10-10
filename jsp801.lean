-- =====================================================================
-- JSP-000801 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the set {1, 2, 4} has all its nonempty subset sums distinct
-- (3 = 1+2, 5 = 1+4, 6 = 2+4, 7 = 1+2+4 are all different):
--   1+2 = 3, 1+4 = 5, 2+4 = 6, 1+2+4 = 7, and 3, 5, 6, 7 pairwise distinct.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp801.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 + 2 = 3) and (1 + 4 = 5)) and (((2 + 4 = 6) and (1 + 2 + 4 = 7)) and ((3 != 5) and (3 != 6)))
def R1 : Prop := (((3 != 7) and (5 != 6)) and (((5 != 7) and (6 != 7)) and True))
theorem jsp801 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (1 + 2 = 3) := by decide
    have h_1 : (1 + 4 = 5) := by decide
    have h_2 : (2 + 4 = 6) := by decide
    have h_3 : (1 + 2 + 4 = 7) := by decide
    have h_4 : (3 != 5) := by decide
    have h_5 : (3 != 6) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (3 != 7) := by decide
    have h_7 : (5 != 6) := by decide
    have h_8 : (5 != 7) := by decide
    have h_9 : (6 != 7) := by decide
    exact <h_6, <h_7, <h_8, h_9>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
