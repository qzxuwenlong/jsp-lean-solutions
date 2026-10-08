-- =====================================================================
-- JSP-000675 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：For a square-root-size subset of an integer interval, how many
--       distinct two-term sums can it have?
--       （整数区间的平方根规模子集可以有多少个不同的两项和？）
--
-- 例证：{1, 2, 4, 8} 是 [1, 8] 的 4 = ⌊√8⌋ 规模子集，其全部 6 个
-- 两项和
--   1+2 = 3、1+4 = 5、1+8 = 9、2+4 = 6、2+8 = 10、4+8 = 12
-- 两两互异（即 6 个不同的两项和）。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp675.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((1 ≥ 1) ∧ ((1 ≤ 8) ∧ (2 ≥ 1))) ∧ (((2 ≤ 8) ∧ (4 ≥ 1)) ∧ ((4 ≤ 8) ∧ (8 ≥ 1)))) ∧ (((8 ≤ 8) ∧ ((1 ≠ 2) ∧ (1 ≠ 4))) ∧ (((1 ≠ 8) ∧ (2 ≠ 4)) ∧ ((2 ≠ 8) ∧ (4 ≠ 8)))))

def R1 : Prop := ((((3 ≠ 5) ∧ ((3 ≠ 9) ∧ (3 ≠ 6))) ∧ (((3 ≠ 10) ∧ (3 ≠ 12)) ∧ ((5 ≠ 9) ∧ (5 ≠ 6)))) ∧ (((5 ≠ 10) ∧ ((5 ≠ 12) ∧ (9 ≠ 6))) ∧ (((9 ≠ 10) ∧ (9 ≠ 12)) ∧ ((6 ≠ 10) ∧ (6 ≠ 12)))))

def R2 : Prop := (10 ≠ 12)

theorem jsp675 (R0 ∧ (R1 ∧ (R2 ∧ True))) :=

  by

  have hr0 : R0 := by

    have h_0 : (1 ≥ 1) := by decide
    have h_1 : (1 ≤ 8) := by decide
    have h_2 : (2 ≥ 1) := by decide
    have h_3 : (2 ≤ 8) := by decide
    have h_4 : (4 ≥ 1) := by decide
    have h_5 : (4 ≤ 8) := by decide
    have h_6 : (8 ≥ 1) := by decide
    have h_7 : (8 ≤ 8) := by decide
    have h_8 : (1 ≠ 2) := by decide
    have h_9 : (1 ≠ 4) := by decide
    have h_10 : (1 ≠ 8) := by decide
    have h_11 : (2 ≠ 4) := by decide
    have h_12 : (2 ≠ 8) := by decide
    have h_13 : (4 ≠ 8) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (3 ≠ 5) := by decide
    have h_15 : (3 ≠ 9) := by decide
    have h_16 : (3 ≠ 6) := by decide
    have h_17 : (3 ≠ 10) := by decide
    have h_18 : (3 ≠ 12) := by decide
    have h_19 : (5 ≠ 9) := by decide
    have h_20 : (5 ≠ 6) := by decide
    have h_21 : (5 ≠ 10) := by decide
    have h_22 : (5 ≠ 12) := by decide
    have h_23 : (9 ≠ 6) := by decide
    have h_24 : (9 ≠ 10) := by decide
    have h_25 : (9 ≠ 12) := by decide
    have h_26 : (6 ≠ 10) := by decide
    have h_27 : (6 ≠ 12) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (10 ≠ 12) := by decide
    exact h_28

  constructor

  · exact hr0

  · exact hr1

  · trivial

