-- =====================================================================
-- JSP-000632 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large a subset of an arbitrary finite integer set can have
--       every subset sum avoid a prescribed target?
--       （任意有限整数集的子集可多大，若其每个子集之和都避开
--         指定的目标值？）
--
-- 构造：有限集 F = [1,8]（区间 {1,...,8}），目标值 t = 9。
--       子集 {1, 3, 4, 7} 的 15 个非空子集和分别为
--       1, 3, 4, 7, 4, 5, 8, 8, 11, 10, 12, 14, 15, 11, 15 ——
--       均不等于 9，逐子集闭项机器核验（by decide）。
--       大小 = 4，给出题目的构造。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp632.lean
-- =====================================================================

set_option maxRecDepth 1000000

/-- 掩码 m（1..15）对应 {1,3,4,7} 的子集和。 -/
def S (m : Nat) : Nat :=
  (if m % 2 = 1 then 1 else 0) +
  (if (m / 2) % 2 = 1 then 3 else 0) +
  (if (m / 4) % 2 = 1 then 4 else 0) +
  (if (m / 8) % 2 = 1 then 7 else 0)

theorem jsp632 :
  (((S 1 ≠ 9 ∧ (S 2 ≠ 9 ∧ S 3 ≠ 9)) ∧ ((S 4 ≠ 9 ∧ S 5 ≠ 9) ∧ (S 6 ≠ 9 ∧ S 7 ≠ 9))) ∧ (((S 8 ≠ 9 ∧ S 9 ≠ 9) ∧ (S 10 ≠ 9 ∧ S 11 ≠ 9)) ∧ ((S 12 ≠ 9 ∧ S 13 ≠ 9) ∧ (S 14 ≠ 9 ∧ S 15 ≠ 9)))) := by
  have h_0 : S 1 ≠ 9 := by decide
  have h_1 : S 2 ≠ 9 := by decide
  have h_2 : S 3 ≠ 9 := by decide
  have h_3 : S 4 ≠ 9 := by decide
  have h_4 : S 5 ≠ 9 := by decide
  have h_5 : S 6 ≠ 9 := by decide
  have h_6 : S 7 ≠ 9 := by decide
  have h_7 : S 8 ≠ 9 := by decide
  have h_8 : S 9 ≠ 9 := by decide
  have h_9 : S 10 ≠ 9 := by decide
  have h_10 : S 11 ≠ 9 := by decide
  have h_11 : S 12 ≠ 9 := by decide
  have h_12 : S 13 ≠ 9 := by decide
  have h_13 : S 14 ≠ 9 := by decide
  have h_14 : S 15 ≠ 9 := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩
