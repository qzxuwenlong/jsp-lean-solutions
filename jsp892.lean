-- =====================================================================
-- JSP-000892 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the composite integer 25 divides a factorial plus one:
--   4! + 1 = 24 + 1 = 25, and 25 | 25, where 25 = 5*5 is composite.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp892.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((1 * 2 * 3 * 4 = 24) and (24 + 1 = 25)) and (((25 = 5 * 5) and (25 % 25 = 0)) and True)
theorem jsp892 (R0 and True) := by
  have hr0 : R0 := by
    have h_0 : (1 * 2 * 3 * 4 = 24) := by decide
    have h_1 : (24 + 1 = 25) := by decide
    have h_2 : (25 = 5 * 5) := by decide
    have h_3 : (25 % 25 = 0) := by decide
    exact <h_0, <h_1, <h_2, h_3>>
  constructor
  . exact hr0
  . trivial
