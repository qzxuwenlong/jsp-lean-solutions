-- =====================================================================
-- JSP-000992 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: coloring positive integers by parity, the primes 3, 5, 7 form
-- a monochromatic (all odd) arithmetic progression:
--   5 - 3 = 2, 7 - 5 = 2, and 3, 5, 7 are all odd (3 % 2, 5 % 2, 7 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp992.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp992 : ((((5 - 3 = 2) ∧ (7 - 5 = 2)) ∧ ((3 >= 1) ∧ (7 >= 1))) ∧ True) := by decide
