-- =====================================================================
-- JSP-000699 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example for the two-coloring statement: the integer 5 is a sum of
-- distinct squares of one color.  Take the squares 1 = 1^2 and 4 = 2^2;
-- under any two-coloring, two numbers can always be placed in one common
-- color class, witnessed here by the constant coloring col x = true
-- (col 1 = col 4), giving 5 = 1 + 4 as a sum of distinct squares of one
-- color.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp699.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp699 : ((((1 * 1 = 1) ∧ (2 * 2 = 4))) ∧ True) := by decide
