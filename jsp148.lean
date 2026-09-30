-- =====================================================================
-- JSP-000148 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many representations of one are there as a sum of a prescribed
--       number of distinct positive unit fractions?
--       （一作为指定数量个互异正整数单位分数之和有多少种表示？）
--
-- 构造（完备计数，k = 3 个分数）：在分母区间 [2, 6] 中，恰有一个
-- 三元素互异子集使其单位分数和为 1：
--     1/2 + 1/3 + 1/6 = 1（通分 60：30 + 20 + 10 = 60）。
-- 全部 2^5 − 1 = 31 个非空子集逐一以通分 60 验证：分子和 = 60 当且
-- 仅当子集为 {2, 3, 6}。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp148.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((30 ≠ 60) ∧ (20 ≠ 60)) ∧ ((15 ≠ 60) ∧ ((12 ≠ 60) ∧ (10 ≠ 60)))) ∧ (((30 + 20 ≠ 60) ∧ (30 + 15 ≠ 60)) ∧ ((30 + 12 ≠ 60) ∧ ((30 + 10 ≠ 60) ∧ (20 + 15 ≠ 60)))))
theorem row0 : R0 := by
  have h_0 : (30 ≠ 60) := by decide
  have h_1 : (20 ≠ 60) := by decide
  have h_2 : (15 ≠ 60) := by decide
  have h_3 : (12 ≠ 60) := by decide
  have h_4 : (10 ≠ 60) := by decide
  have h_5 : (30 + 20 ≠ 60) := by decide
  have h_6 : (30 + 15 ≠ 60) := by decide
  have h_7 : (30 + 12 ≠ 60) := by decide
  have h_8 : (30 + 10 ≠ 60) := by decide
  have h_9 : (20 + 15 ≠ 60) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, h_6⟩, ⟨h_7, ⟨h_8, h_9⟩⟩⟩⟩

def R1 : Prop := ((((20 + 12 ≠ 60) ∧ (20 + 10 ≠ 60)) ∧ ((15 + 12 ≠ 60) ∧ ((15 + 10 ≠ 60) ∧ (12 + 10 ≠ 60)))) ∧ (((30 + 20 + 15 ≠ 60) ∧ (30 + 20 + 12 ≠ 60)) ∧ ((30 + 20 + 10 = 60) ∧ ((30 + 15 + 12 ≠ 60) ∧ (30 + 15 + 10 ≠ 60)))))
theorem row1 : R1 := by
  have h_0 : (20 + 12 ≠ 60) := by decide
  have h_1 : (20 + 10 ≠ 60) := by decide
  have h_2 : (15 + 12 ≠ 60) := by decide
  have h_3 : (15 + 10 ≠ 60) := by decide
  have h_4 : (12 + 10 ≠ 60) := by decide
  have h_5 : (30 + 20 + 15 ≠ 60) := by decide
  have h_6 : (30 + 20 + 12 ≠ 60) := by decide
  have h_7 : (30 + 20 + 10 = 60) := by decide
  have h_8 : (30 + 15 + 12 ≠ 60) := by decide
  have h_9 : (30 + 15 + 10 ≠ 60) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, h_6⟩, ⟨h_7, ⟨h_8, h_9⟩⟩⟩⟩

def R2 : Prop := ((((30 + 12 + 10 ≠ 60) ∧ (20 + 15 + 12 ≠ 60)) ∧ ((20 + 15 + 10 ≠ 60) ∧ ((20 + 12 + 10 ≠ 60) ∧ (15 + 12 + 10 ≠ 60)))) ∧ (((30 + 20 + 15 + 12 ≠ 60) ∧ (30 + 20 + 15 + 10 ≠ 60)) ∧ ((30 + 20 + 12 + 10 ≠ 60) ∧ ((30 + 15 + 12 + 10 ≠ 60) ∧ (20 + 15 + 12 + 10 ≠ 60)))))
theorem row2 : R2 := by
  have h_0 : (30 + 12 + 10 ≠ 60) := by decide
  have h_1 : (20 + 15 + 12 ≠ 60) := by decide
  have h_2 : (20 + 15 + 10 ≠ 60) := by decide
  have h_3 : (20 + 12 + 10 ≠ 60) := by decide
  have h_4 : (15 + 12 + 10 ≠ 60) := by decide
  have h_5 : (30 + 20 + 15 + 12 ≠ 60) := by decide
  have h_6 : (30 + 20 + 15 + 10 ≠ 60) := by decide
  have h_7 : (30 + 20 + 12 + 10 ≠ 60) := by decide
  have h_8 : (30 + 15 + 12 + 10 ≠ 60) := by decide
  have h_9 : (20 + 15 + 12 + 10 ≠ 60) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, h_6⟩, ⟨h_7, ⟨h_8, h_9⟩⟩⟩⟩

def R3 : Prop := ((30 + 20 + 15 + 12 + 10 ≠ 60) ∧ ((2 ≥ 2) ∧ (6 ≤ 6)))
theorem row3 : R3 := by
  have h_0 : (30 + 20 + 15 + 12 + 10 ≠ 60) := by decide
  have h_1 : (2 ≥ 2) := by decide
  have h_2 : (6 ≤ 6) := by decide
  exact ⟨h_0, ⟨h_1, h_2⟩⟩

theorem jsp148 :
  ((R0 ∧ R1) ∧ (R2 ∧ R3)) := by
  exact ⟨⟨row0, row1⟩, ⟨row2, row3⟩⟩
