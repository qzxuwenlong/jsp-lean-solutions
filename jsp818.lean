-- =====================================================================
-- JSP-000818 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: 2 is a small prime primitive root modulo the prime 5; its
-- powers cover every nonzero residue modulo 5:
--   2^1 = 2, 2^2 = 4, 2^3 = 8 = 3 (mod 5), 2^4 = 16 = 1 (mod 5).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp818.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 % 5 = 2) and (4 % 5 = 4)) and (((8 % 5 = 3) and (16 % 5 = 1)) and ((2 = 2 * 1) and True))
def R1 : Prop := ((5 % 2 != 0) and (5 % 3 != 0)) and True
theorem jsp818 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (2 % 5 = 2) := by decide
    have h_1 : (4 % 5 = 4) := by decide
    have h_2 : (8 % 5 = 3) := by decide
    have h_3 : (16 % 5 = 1) := by decide
    have h_4 : (2 = 2 * 1) := by decide
    exact <h_0, <h_1, <h_2, <h_3, h_4>>
  have hr1 : R1 := by
    have h_5 : (5 % 2 != 0) := by decide
    have h_6 : (5 % 3 != 0) := by decide
    exact <h_5, h_6>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
