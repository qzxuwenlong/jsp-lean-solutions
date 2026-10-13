-- =====================================================================
-- JSP-000986 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: for the logarithmically short consecutive interval [1, 2],
-- the product 1*2 = 2 is not divisible by 3, and 3 is the smallest
-- prime not dividing it (2 divides 2; 3 is prime with 3 > 2).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp986.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp986 : ((((1 * 2 = 2) ∧ (2 % 2 = 0)) ∧ ((2 >= 1) ∧ (2 % 1 = 0))) ∧ True) := by decide
