-- =====================================================================
-- JSP-000054 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Cluster-prime examples:
--   p = 5: the only positive even integer at most p-3 = 2, namely 2,
--          is a difference of two primes at most 5: 2 = 5 - 3.
--   p = 7: 2 = 7 - 5 and 4 = 7 - 3 (both even integers at most 4).
-- Primality of 3, 5, 7 witnessed by absence of small factors
-- (7 % 2, 7 % 3 nonzero; 5 % 2, 3 % 2 nonzero).
-- All closed-form by decide.
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp54.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((5 % 2 != 0) and (3 % 2 != 0)) and (((2 = 5 - 3) and (2 <= 2)) and ((5 <= 5) and (3 <= 5)))
def R1 : Prop := ((7 % 2 != 0) and (7 % 3 != 0)) and (((5 % 2 != 0) and (2 = 7 - 5)) and ((4 = 7 - 3) and (2 <= 4)))
def R2 : Prop := ((4 <= 4) and (7 <= 7)) and (((5 <= 7) and (3 <= 7)) and True)
theorem jsp54 (R0 and (R1 and (R2 and True))) := by
  have hr0 : R0 := by
    have h_0 : (5 % 2 != 0) := by decide
    have h_1 : (3 % 2 != 0) := by decide
    have h_2 : (2 = 5 - 3) := by decide
    have h_3 : (2 <= 2) := by decide
    have h_4 : (5 <= 5) := by decide
    have h_5 : (3 <= 5) := by decide
    exact <h_0, <h_1, <h_2, <h_3, <h_4, h_5>>>>
  have hr1 : R1 := by
    have h_6 : (7 % 2 != 0) := by decide
    have h_7 : (7 % 3 != 0) := by decide
    have h_8 : (5 % 2 != 0) := by decide
    have h_9 : (2 = 7 - 5) := by decide
    have h_10 : (4 = 7 - 3) := by decide
    have h_11 : (2 <= 4) := by decide
    exact <h_6, <h_7, <h_8, <h_9, <h_10, h_11>>>>
  have hr2 : R2 := by
    have h_12 : (4 <= 4) := by decide
    have h_13 : (7 <= 7) := by decide
    have h_14 : (5 <= 7) := by decide
    have h_15 : (3 <= 7) := by decide
    exact <h_12, <h_13, <h_14, h_15>>
  constructor
  . exact hr0
  . constructor
  . exact hr1
  . constructor
  . exact hr2
  . trivial
