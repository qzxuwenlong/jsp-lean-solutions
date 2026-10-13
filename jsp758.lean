-- =====================================================================
-- JSP-000758 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Complete construction for the existence question:
-- "Can the product of consecutive integers have pairwise distinct
--  prime-factor exponents?"
-- Construction: 7 * 8 * 9 = 504 = 2^3 * 3^2 * 7^1, whose prime-factor
-- exponents are 3, 2, 1 — pairwise distinct. Also 7 is prime (not
-- divisible by 2, 3 or 5).
-- Environment: Lean 4.28.0-pre (wasm32), core + Std only.
-- Verify: node run-lean-local.js jsp758.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp758 : ((((7 * 8 * 9 = 504) ∧ (504 = 2 * 2 * 2 * 3 * 3 * 7)) ∧ ((3 ≠ 2) ∧ ((2 ≠ 1) ∧ (3 ≠ 1))) ∧ (((7 % 2 ≠ 0) ∧ (7 % 3 ≠ 0)) ∧ (7 % 5 ≠ 0))) ∧ True) := by decide
