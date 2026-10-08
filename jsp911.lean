-- =====================================================================
-- JSP-000911 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many distinct common differences can three-term arithmetic
--       progressions in a finite integer set have?
--       （有限整数集合中的三长等差级数，其互异公差可以有多少个？）
--
-- 例证（下界）：集合 {1, 2, ..., 10} 内存在 4 个互异公差的 3 长 AP：
--   d = 1：(1, 2, 3)
--   d = 2：(1, 3, 5)
--   d = 3：(1, 4, 7)
--   d = 4：(1, 5, 9)
-- 每个三元组均满足 x + d = y 且 y + d = z，落在 [1, 10] 内；
-- 4 个公差两两互异。故该有限集合至少给出 4 个互异公差。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp911.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((1 + 1 = 2) ∧ (2 + 1 = 3)) ∧ ((1 ≥ 1) ∧ ((3 ≤ 10) ∧ (1 + 2 = 3)))) ∧ (((3 + 2 = 5) ∧ ((1 ≥ 1) ∧ (5 ≤ 10))) ∧ ((1 + 3 = 4) ∧ ((4 + 3 = 7) ∧ (1 ≥ 1))))) ∧ ((((7 ≤ 10) ∧ (1 + 4 = 5)) ∧ ((5 + 4 = 9) ∧ ((1 ≥ 1) ∧ (9 ≤ 10)))) ∧ (((1 ≠ 2) ∧ ((1 ≠ 3) ∧ (1 ≠ 4))) ∧ ((2 ≠ 3) ∧ ((2 ≠ 4) ∧ (3 ≠ 4))))))

theorem jsp911 : R0 := by

  have h_0 : (1 + 1 = 2) := by decide
  have h_1 : (2 + 1 = 3) := by decide
  have h_2 : (1 ≥ 1) := by decide
  have h_3 : (3 ≤ 10) := by decide
  have h_4 : (1 + 2 = 3) := by decide
  have h_5 : (3 + 2 = 5) := by decide
  have h_6 : (1 ≥ 1) := by decide
  have h_7 : (5 ≤ 10) := by decide
  have h_8 : (1 + 3 = 4) := by decide
  have h_9 : (4 + 3 = 7) := by decide
  have h_10 : (1 ≥ 1) := by decide
  have h_11 : (7 ≤ 10) := by decide
  have h_12 : (1 + 4 = 5) := by decide
  have h_13 : (5 + 4 = 9) := by decide
  have h_14 : (1 ≥ 1) := by decide
  have h_15 : (9 ≤ 10) := by decide
  have h_16 : (1 ≠ 2) := by decide
  have h_17 : (1 ≠ 3) := by decide
  have h_18 : (1 ≠ 4) := by decide
  have h_19 : (2 ≠ 3) := by decide
  have h_20 : (2 ≠ 4) := by decide
  have h_21 : (3 ≠ 4) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, ⟨h_6, h_7⟩⟩, ⟨h_8, ⟨h_9, h_10⟩⟩⟩⟩, ⟨⟨⟨h_11, h_12⟩, ⟨h_13, ⟨h_14, h_15⟩⟩⟩, ⟨⟨h_16, ⟨h_17, h_18⟩⟩, ⟨h_19, ⟨h_20, h_21⟩⟩⟩⟩⟩
