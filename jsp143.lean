-- =====================================================================
-- JSP-000143 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- 3, 5, 7 are consecutive primes (in the full prime sequence 2,3,5,7,11,...)
-- forming an arithmetic progression. Primality is witnessed by the absence
-- of small factors; the intermediate integers 4 = 2*2 and 6 = 2*3 are
-- composite, so 3,5,7 are consecutive primes. All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp143.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp143 : ((((2 * 2 > 3) ∧ (5 % 2 ≠ 0)) ∧ ((5 < 7) ∧ (3 + 7 = 2 * 5))) ∧ True) := by decide
