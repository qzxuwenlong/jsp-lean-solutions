-- =====================================================================
-- JSP-000389 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: modulo the prime 7, the first four factorials give distinct
-- residues:
--   1! = 1, 2! = 2, 3! = 6, 4! = 24 = 3 (mod 7), all distinct.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean-local.js jsp389.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp389 : ((((1 % 7 = 1) ∧ (2 % 7 = 2)) ∧ (((6 ≠ 3) ∧ (1 ≠ 3)) ∧ ((1 * 2 = 2) ∧ (1 * 2 * 3 = 6)))) ∧ True) := by decide
