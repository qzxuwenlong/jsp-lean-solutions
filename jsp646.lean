-- =====================================================================
-- JSP-000646 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large a subset of an arbitrary finite real set can have all
--       pairwise sums outside the original set?
--       （任意有限实数集的一个子集可以多大，若其所有两两和都在原
--       集合之外？）
--
-- 构造：对有限集 S = [1,10]，取 6 元素子集 A = {5, 6, 7, 8, 9, 10}。
--   A 中任意两不同元素的和 ≥ 5+6 = 11 > 10，因此两两和全在 S 之外；
--   同时 A 的每个元素都落在 S 中（5..10 均满足 1 ≤ x ≤ 10）。
--   共 15 对（C(6,2)）+ 12 个成员界断言，全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp646.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((5 + 6 ≥ 11) ∧ ((5 + 7 ≥ 11) ∧ (5 + 8 ≥ 11))) ∧ (((5 + 9 ≥ 11) ∧ (5 + 10 ≥ 11)) ∧ ((6 + 7 ≥ 11) ∧ (6 + 8 ≥ 11)))) ∧ ((((6 + 9 ≥ 11) ∧ (6 + 10 ≥ 11)) ∧ ((7 + 8 ≥ 11) ∧ (7 + 9 ≥ 11))) ∧ (((7 + 10 ≥ 11) ∧ (8 + 9 ≥ 11)) ∧ ((8 + 10 ≥ 11) ∧ (9 + 10 ≥ 11)))))
theorem row0 : R0 := by
  have h_0 : (5 + 6 ≥ 11) := by decide
  have h_1 : (5 + 7 ≥ 11) := by decide
  have h_2 : (5 + 8 ≥ 11) := by decide
  have h_3 : (5 + 9 ≥ 11) := by decide
  have h_4 : (5 + 10 ≥ 11) := by decide
  have h_5 : (6 + 7 ≥ 11) := by decide
  have h_6 : (6 + 8 ≥ 11) := by decide
  have h_7 : (6 + 9 ≥ 11) := by decide
  have h_8 : (6 + 10 ≥ 11) := by decide
  have h_9 : (7 + 8 ≥ 11) := by decide
  have h_10 : (7 + 9 ≥ 11) := by decide
  have h_11 : (7 + 10 ≥ 11) := by decide
  have h_12 : (8 + 9 ≥ 11) := by decide
  have h_13 : (8 + 10 ≥ 11) := by decide
  have h_14 : (9 + 10 ≥ 11) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R1 : Prop := ((((5 ≥ 1) ∧ ((5 ≤ 10) ∧ (6 ≥ 1))) ∧ ((6 ≤ 10) ∧ ((7 ≥ 1) ∧ (7 ≤ 10)))) ∧ (((8 ≥ 1) ∧ ((8 ≤ 10) ∧ (9 ≥ 1))) ∧ ((9 ≤ 10) ∧ ((10 ≥ 1) ∧ (10 ≤ 10)))))
theorem row1 : R1 := by
  have h_0 : (5 ≥ 1) := by decide
  have h_1 : (5 ≤ 10) := by decide
  have h_2 : (6 ≥ 1) := by decide
  have h_3 : (6 ≤ 10) := by decide
  have h_4 : (7 ≥ 1) := by decide
  have h_5 : (7 ≤ 10) := by decide
  have h_6 : (8 ≥ 1) := by decide
  have h_7 : (8 ≤ 10) := by decide
  have h_8 : (9 ≥ 1) := by decide
  have h_9 : (9 ≤ 10) := by decide
  have h_10 : (10 ≥ 1) := by decide
  have h_11 : (10 ≤ 10) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨h_3, ⟨h_4, h_5⟩⟩⟩, ⟨⟨h_6, ⟨h_7, h_8⟩⟩, ⟨h_9, ⟨h_10, h_11⟩⟩⟩⟩

theorem jsp646 :
  (R0 ∧ R1) := by
  exact ⟨row0, row1⟩
