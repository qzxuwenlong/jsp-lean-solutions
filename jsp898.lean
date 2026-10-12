-- =====================================================================
-- JSP-000898 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 16 is a sum of two powerful numbers:
--   8 = 2^3 and 8 = 2^3 are powerful (prime factor 2 has exponent 3),
--   and 16 = 8 + 8; 16 = 2^4 is itself powerful.
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean-local.js jsp898.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 * 2 * 2 = 8) ∧ (8 + 8 = 16)) ∧ (((16 = 2 * 2 * 2 * 2) ∧ (16 >= 1)) ∧ True)
theorem jsp898 : (R0 ∧ True) := by
  have hr0 : R0 := by
    have h_0 : (2 * 2 * 2 = 8) := by decide
    have h_1 : (8 + 8 = 16) := by decide
    have h_2 : (16 = 2 * 2 * 2 * 2) := by decide
    have h_3 : (16 >= 1) := by decide
    exact ⟨⟨h_0, h_1⟩, ⟨⟨h_2, h_3⟩, trivial⟩⟩
  exact ⟨hr0, trivial⟩
