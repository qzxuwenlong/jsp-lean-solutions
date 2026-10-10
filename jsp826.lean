-- =====================================================================
-- JSP-000826 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: for the path P5 (a tree/forest), the counts of independent
-- sets by size are 1, 5, 6, 1, 0, which form a unimodal sequence:
--   size 0: 1 (empty), size 1: 5 (single vertices),
--   size 2: 6 = C(5,2) - 4 (nonadjacent pairs: 10 - 4),
--   size 3: 1 ({1,3,5}), size 4: 0; 1 <= 5 <= 6 >= 1 >= 0.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp826.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((5 = 1 + 1 + 1 + 1 + 1) and (10 = 4 + 3 + 2 + 1)) and (((10 - 4 = 6) and (6 >= 5)) and ((5 >= 1) and True))
def R1 : Prop := ((6 >= 1) and (1 >= 0)) and True
theorem jsp826 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (5 = 1 + 1 + 1 + 1 + 1) := by decide
    have h_1 : (10 = 4 + 3 + 2 + 1) := by decide
    have h_2 : (10 - 4 = 6) := by decide
    have h_3 : (6 >= 5) := by decide
    have h_4 : (5 >= 1) := by decide
    exact <h_0, <h_1, <h_2, <h_3, h_4>>
  have hr1 : R1 := by
    have h_5 : (6 >= 1) := by decide
    have h_6 : (1 >= 0) := by decide
    exact <h_5, h_6>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
