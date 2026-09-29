-- =====================================================================
-- JSP-000874 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How can a target integer be represented as the sum of an initial
--       segment of another integer's ordered nontrivial divisors?
--       （目标整数如何表示为另一整数有序非平凡除数的初始段之和？）
--
-- 构造：30 的有序非平凡除数为
--     [2, 3, 5, 6, 10, 15, 30]。
--   目标整数 10 = 2 + 3 + 5 = 初始段 [2,3,5] 之和（前 3 个非平凡
--   除数）。同时验证列表项均为 30 的非平凡除数（30 mod d = 0，
--   不含 1）且严格递增有序。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp874.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((2 + 3 + 5 = 10) ∧ (30 % 2 = 0)) ∧ ((30 % 3 = 0) ∧ ((30 % 5 = 0) ∧ (2 ≥ 2)))) ∧ (((5 ≤ 30) ∧ (30 % 6 = 0)) ∧ ((30 % 10 = 0) ∧ ((30 % 15 = 0) ∧ (30 % 30 = 0))))) ∧ ((((30 % 2 = 0) ∧ (30 % 3 = 0)) ∧ ((30 % 5 = 0) ∧ ((2 < 3) ∧ (3 < 5)))) ∧ (((5 < 6) ∧ (6 < 10)) ∧ ((10 < 15) ∧ ((15 < 30) ∧ (30 ≠ 1))))))

theorem jsp874 : R0 := by

  have h_0 : (2 + 3 + 5 = 10) := by decide
  have h_1 : (30 % 2 = 0) := by decide
  have h_2 : (30 % 3 = 0) := by decide
  have h_3 : (30 % 5 = 0) := by decide
  have h_4 : (2 ≥ 2) := by decide
  have h_5 : (5 ≤ 30) := by decide
  have h_6 : (30 % 6 = 0) := by decide
  have h_7 : (30 % 10 = 0) := by decide
  have h_8 : (30 % 15 = 0) := by decide
  have h_9 : (30 % 30 = 0) := by decide
  have h_10 : (30 % 2 = 0) := by decide
  have h_11 : (30 % 3 = 0) := by decide
  have h_12 : (30 % 5 = 0) := by decide
  have h_13 : (2 < 3) := by decide
  have h_14 : (3 < 5) := by decide
  have h_15 : (5 < 6) := by decide
  have h_16 : (6 < 10) := by decide
  have h_17 : (10 < 15) := by decide
  have h_18 : (15 < 30) := by decide
  have h_19 : (30 ≠ 1) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, h_6⟩, ⟨h_7, ⟨h_8, h_9⟩⟩⟩⟩, ⟨⟨⟨h_10, h_11⟩, ⟨h_12, ⟨h_13, h_14⟩⟩⟩, ⟨⟨h_15, h_16⟩, ⟨h_17, ⟨h_18, h_19⟩⟩⟩⟩⟩
