-- =====================================================================
-- JSP-000985 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Example: modulo the prime 7, the modular inverses of 1, 2, 3 are
-- 1, 4, 5 (2*4 = 8 ≡ 1 and 3*5 = 15 ≡ 1 mod 7); the subset sums of
-- {1, 4, 5} cover every nonzero residue modulo 7:
--   1, 4, 5, 1+4 ≡ 5, 1+5 ≡ 6, 4+5 ≡ 2, 1+4+5 ≡ 3 (mod 7).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp985.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((2 * 4 = 8) and (8 % 7 = 1)) and (((3 * 5 = 15) and (15 % 7 = 1)) and ((4 % 7 = 4) and (5 % 7 = 5)))
def R1 : Prop := (((1 + 4) % 7 = 5) and ((1 + 5) % 7 = 6)) and ((((4 + 5) % 7 = 2) and ((1 + 4 + 5) % 7 = 3)) and True)
theorem jsp985 (R0 and (R1 and True)) := by
  have hr0 : R0 := by
    have h_0 : (2 * 4 = 8) := by decide
    have h_1 : (8 % 7 = 1) := by decide
    have h_2 : (3 * 5 = 15) := by decide
    have h_3 : (15 % 7 = 1) := by decide
    have h_4 : (4 % 7 = 4) := by decide
    have h_5 : (5 % 7 = 5) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : ((1 + 4) % 7 = 5) := by decide
    have h_7 : ((1 + 5) % 7 = 6) := by decide
    have h_8 : ((4 + 5) % 7 = 2) := by decide
    have h_9 : ((1 + 4 + 5) % 7 = 3) := by decide
    exact <h_6, <h_7, <h_8, h_9>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . trivial
