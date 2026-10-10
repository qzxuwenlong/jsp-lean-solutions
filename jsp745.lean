-- =====================================================================
-- JSP-000745 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example for coloring the integers so that no same-colored pair has
-- difference in a prescribed sparse set: take the parity coloring
--   col n := (n % 2 = 0)
-- and the sparse difference set {1}.  Within [1, 4], every pair at
-- distance 1 has distinct colors:
--   col 1 != col 2,  col 2 != col 3,  col 3 != col 4.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp745.lean
-- =====================================================================

set_option maxRecDepth 1000000

def col (n : Nat) : Bool := n % 2 = 0

def R0 : Prop := ((col 1 != col 2) and (col 2 != col 3)) and ((col 3 != col 4) and True)
theorem jsp745 (R0 and True) := by
  have hr0 : R0 := by
    have h_0 : (col 1 != col 2) := by decide
    have h_1 : (col 2 != col 3) := by decide
    have h_2 : (col 3 != col 4) := by decide
    exact <h_0, <h_1, h_2>>
  constructor
  . exact hr0
  . trivial
