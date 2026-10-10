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

def R0 : Prop := ((7 < 8) and (10 < 11)) and (((8 = 2 * 2 * 2) and (9 = 3 * 3)) and ((10 = 2 * 5) and (7 % 2 != 0)))
def R1 : Prop := ((7 % 3 != 0) and (11 % 2 != 0)) and (((11 % 3 != 0) and (11 % 5 != 0)) and ((8 % 2 = 0) and (9 % 3 = 0)))
def R2 : Prop := ((10 % 2 = 0) and (5 >= 1)) and True
theorem jsp774 (R0 and (R1 and (R2 and True))) := by
  have hr0 : R0 := by
    have h_0 : (7 < 8) := by decide
    have h_1 : (10 < 11) := by decide
    have h_2 : (8 = 2 * 2 * 2) := by decide
    have h_3 : (9 = 3 * 3) := by decide
    have h_4 : (10 = 2 * 5) := by decide
    have h_5 : (7 % 2 != 0) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (7 % 3 != 0) := by decide
    have h_7 : (11 % 2 != 0) := by decide
    have h_8 : (11 % 3 != 0) := by decide
    have h_9 : (11 % 5 != 0) := by decide
    have h_10 : (8 % 2 = 0) := by decide
    have h_11 : (9 % 3 = 0) := by decide
    exact <h_6, <h_7, <h_8, <h_9, <h_10, h_11>>>>
  have hr2 : R2 := by
    have h_12 : (10 % 2 = 0) := by decide
    have h_13 : (5 >= 1) := by decide
    exact <h_12, h_13>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . constructor
  . exact hr2
  . trivial
