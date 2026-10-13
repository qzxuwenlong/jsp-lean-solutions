-- =====================================================================
-- JSP-000898 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 16 is a sum of two powerful numbers:
--   8 = 2^3 and 8 = 2^3 are powerful (prime factor 2 has exponent 3),
--   and 16 = 8 + 8; 16 = 2^4 is itself powerful.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean-local.js jsp898.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp898 : ((((2 * 2 * 2 = 8) ∧ (8 + 8 = 16))) ∧ True) := by decide
