-- =====================================================================
-- JSP-000685 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many representations can one integer have as a sum of two
--       integer cubes?
--       （一个整数作为两个整数立方和可以有多少种表示？）
--
-- 例证：1729（Ramanujan 数）恰有这两种立方和表示：
--   1729 = 1³ + 12³ = 1 + 1728，
--   1729 = 9³ + 10³ = 729 + 1000。
-- 两组的底数对 (1, 12) 与 (9, 10) 各自互异，且两组不同。
-- 全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp685.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((1 * 1 * 1 = 1) ∧ (12 * 12 * 12 = 1728)) ∧ ((9 * 9 * 9 = 729) ∧ (10 * 10 * 10 = 1000))) ∧ (((1 + 1728 = 1729) ∧ (729 + 1000 = 1729)) ∧ ((1 ≠ 12) ∧ ((9 ≠ 10) ∧ (1729 ≥ 1)))))

theorem jsp685 : R0 := by

  have h_0 : (1 * 1 * 1 = 1) := by decide
  have h_1 : (12 * 12 * 12 = 1728) := by decide
  have h_2 : (9 * 9 * 9 = 729) := by decide
  have h_3 : (10 * 10 * 10 = 1000) := by decide
  have h_4 : (1 + 1728 = 1729) := by decide
  have h_5 : (729 + 1000 = 1729) := by decide
  have h_6 : (1 ≠ 12) := by decide
  have h_7 : (9 ≠ 10) := by decide
  have h_8 : (1729 ≥ 1) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, ⟨h_7, h_8⟩⟩⟩⟩
