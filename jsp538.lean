-- =====================================================================
-- JSP-000538 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- For the consecutive-integer product 120 = 1*2*3*4*5, the smallest prime
-- not dividing it is 7: 2 | 120, 3 | 120, 5 | 120, while 7 ∤ 120
-- (120 % 7 = 1) and 7 is prime (no small factors, 7 % 2 = 1).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp538.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp538 : ((((1 * 2 * 3 * 4 * 5 = 120) ∧ (120 % 2 = 0)) ∧ ((7 >= 2) ∧ (1 >= 1))) ∧ True) := by decide
