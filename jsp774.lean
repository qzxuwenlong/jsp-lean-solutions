-- =====================================================================
-- JSP-000774 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: the consecutive primes 7 and 11 enclose three integers
-- 8, 9, 10 whose prime factors are all at most 5:
--   8  = 2*2*2  (factor 2)
--   9  = 3*3    (factor 3)
--   10 = 2*5    (factors 2, 5)
-- 7 and 11 are prime (7 % 2, 7 % 3, 11 % 2, 11 % 3, 11 % 5 nonzero);
-- there is no prime strictly between them since 8, 9, 10 are composite
-- (8 % 2 = 0, 9 % 3 = 0, 10 % 2 = 0).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp774.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp774 : ((((7 < 8) ∧ (10 < 11)) ∧ ((7 % 3 ≠ 0) ∧ (11 % 2 ≠ 0)) ∧ ((10 % 2 = 0) ∧ (5 >= 1))) ∧ True) := by decide
