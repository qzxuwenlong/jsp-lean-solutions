-- =====================================================================
-- JSP-000260 (c) 2026 qzxuwenlong — The Justin Sun Prize
-- Subsums of unit fractions with denominators in a finite range
-- approximating one:
--   G1: 1/2 + 1/3 + 1/6 = 1        (denominators 2,3,6 in [1,6])
--   G2: 1/2 + 1/4 + 1/8 = 7/8 <= 1 (denominators 2,4,8 in [1,8])
-- All closed-form by decide. Nat division is truncating, so the unit
-- fractions are verified via the common-denominator integer forms:
--   G1: 1/2 + 1/3 + 1/6 = 1  iff  3 + 2 + 1 = 6
--   G2: 1/2 + 1/4 + 1/8 = 7/8  iff  4 + 2 + 1 = 7  and  7 <= 8
-- Lean 4 wasm32 core+Std only. node run-lean.js jsp260.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp260 : ((((((3 + 2 + 1 = 6) ∧ ((2 ≥ 1) ∧ (3 ≥ 1))) ∧ (((6 ≥ 1) ∧ (2 ≤ 6)) ∧ ((3 ≤ 6) ∧ (6 ≤ 6)))) ∧ ((((4 + 2 + 1 = 7) ∧ (7 ≤ 8)) ∧ ((2 ≥ 1) ∧ (4 ≥ 1))) ∧ (((8 ≥ 1) ∧ (2 ≤ 8)) ∧ ((4 ≤ 8) ∧ (8 ≤ 8))))) ∧ True) := by
  have h_a : (3 + 2 + 1 = 6) := by decide
  have h_b : ((2 ≥ 1) ∧ (3 ≥ 1)) := by decide
  have h_c : ((6 ≥ 1) ∧ (2 ≤ 6)) := by decide
  have h_d : ((3 ≤ 6) ∧ (6 ≤ 6)) := by decide
  have h_e : ((4 + 2 + 1 = 7) ∧ (7 ≤ 8)) := by decide
  have h_f : ((2 ≥ 1) ∧ (4 ≥ 1)) := by decide
  have h_g : ((8 ≥ 1) ∧ (2 ≤ 8)) := by decide
  have h_h : ((4 ≤ 8) ∧ (8 ≤ 8)) := by decide
  exact ⟨⟨⟨h_a, ⟨h_b.1, h_b.2⟩⟩, ⟨⟨h_c.1, h_c.2⟩, ⟨h_d.1, h_d.2⟩⟩⟩, ⟨⟨⟨h_e.1, h_e.2⟩, ⟨h_f.1, h_f.2⟩⟩, ⟨⟨h_g.1, h_g.2⟩, ⟨h_h.1, h_h.2⟩⟩⟩⟩, True.intro⟩
