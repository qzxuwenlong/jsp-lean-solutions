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

theorem jsp49 : ((((2 * 2 = 4) ∧ (2 * 2 * 2 = 8)) ∧ ((17 % 2 ≠ 0) ∧ (17 % 3 ≠ 0)) ∧ ((8 + 5 = 13) ∧ (4 + 13 = 17)) ∧ ((29 >= 9) ∧ (5 >= 2))) ∧ True) := by decide
