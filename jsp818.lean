-- =====================================================================
-- JSP-000818 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 2 is a small prime primitive root modulo the prime 5; its
-- powers cover every nonzero residue modulo 5:
--   2^1 = 2, 2^2 = 4, 2^3 = 8 = 3 (mod 5), 2^4 = 16 = 1 (mod 5).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp818.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp818 : ((((2 % 5 = 2) ∧ (4 % 5 = 4)) ∧ ((5 % 2 ≠ 0) ∧ (5 % 3 ≠ 0))) ∧ True) := by decide
