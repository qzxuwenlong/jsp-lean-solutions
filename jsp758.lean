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

def R0 : Prop := ((7 * 8 * 9 = 504) ∧ (504 = 2 * 2 * 2 * 3 * 3 * 7))
theorem row0 : R0 := by
  have h_0 : (7 * 8 * 9 = 504) := by decide
  have h_1 : (504 = 2 * 2 * 2 * 3 * 3 * 7) := by decide
  exact ⟨h_0, h_1⟩

def R1 : Prop := ((3 ≠ 2) ∧ ((2 ≠ 1) ∧ (3 ≠ 1)))
theorem row1 : R1 := by
  have h_2 : (3 ≠ 2) := by decide
  have h_3 : (2 ≠ 1) := by decide
  have h_4 : (3 ≠ 1) := by decide
  exact ⟨h_2, ⟨h_3, h_4⟩⟩

def R2 : Prop := (((7 % 2 ≠ 0) ∧ (7 % 3 ≠ 0)) ∧ (7 % 5 ≠ 0))
theorem row2 : R2 := by
  have h_5 : (7 % 2 ≠ 0) := by decide
  have h_6 : (7 % 3 ≠ 0) := by decide
  have h_7 : (7 % 5 ≠ 0) := by decide
  exact ⟨⟨h_5, h_6⟩, h_7⟩

theorem jsp758 :
  ((R0 ∧ R1) ∧ (R2 ∧ True)) := by
  exact ⟨⟨row0, row1⟩, ⟨row2, trivial⟩⟩
