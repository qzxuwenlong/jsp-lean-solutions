-- =====================================================================
-- JSP-000550 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Must two disjoint equal-length intervals of consecutive integers
--       have different least common multiples?
--       （两个不相交的等长连续整数区间，其最小公倍数必然不同吗？）
--
-- 例证（支持"不同"方向）：两对不相交等长区间的最小公倍数均不相同：
--   [1, 3] = {1, 2, 3}：lcm = 6
--   [4, 6] = {4, 5, 6}：lcm = 60，且 4 > 3（两区间不相交），6 ≠ 60。
--   [2, 5] = {2, 3, 4, 5}：lcm = 60
--   [6, 9] = {6, 7, 8, 9}：lcm = 504，且 6 > 5（两区间不相交），
--   60 ≠ 504。
-- 每个区间的元素界逐一验证；lcm 由嵌套 Nat.lcm 闭项计算。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp550.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((((Nat.lcm (Nat.lcm 1 2) 3 = 6) ∧ (Nat.lcm (Nat.lcm 4 5) 6 = 60)) ∧ ((6 ≠ 60) ∧ (4 > 3))) ∧ (((1 ≥ 1) ∧ (1 ≤ 3)) ∧ ((2 ≥ 1) ∧ ((2 ≤ 3) ∧ (3 ≥ 1))))) ∧ ((((3 ≤ 3) ∧ (4 ≥ 4)) ∧ ((4 ≤ 6) ∧ (5 ≥ 4))) ∧ (((5 ≤ 6) ∧ (6 ≥ 4)) ∧ ((6 ≤ 6) ∧ ((Nat.lcm (Nat.lcm (Nat.lcm 2 3) 4) 5 = 60) ∧ (Nat.lcm (Nat.lcm (Nat.lcm 6 7) 8) 9 = 504)))))) ∧ (((((60 ≠ 504) ∧ (6 > 5)) ∧ ((2 ≥ 2) ∧ (2 ≤ 5))) ∧ (((3 ≥ 2) ∧ (3 ≤ 5)) ∧ ((4 ≥ 2) ∧ ((4 ≤ 5) ∧ (5 ≥ 2))))) ∧ ((((5 ≤ 5) ∧ (6 ≥ 6)) ∧ ((6 ≤ 9) ∧ (7 ≥ 6))) ∧ (((7 ≤ 9) ∧ (8 ≥ 6)) ∧ ((8 ≤ 9) ∧ ((9 ≥ 6) ∧ (9 ≤ 9)))))))

theorem jsp550 : R0 := by

  have h_0 : (Nat.lcm (Nat.lcm 1 2) 3 = 6) := by decide
  have h_1 : (Nat.lcm (Nat.lcm 4 5) 6 = 60) := by decide
  have h_2 : (6 ≠ 60) := by decide
  have h_3 : (4 > 3) := by decide
  have h_4 : (1 ≥ 1) := by decide
  have h_5 : (1 ≤ 3) := by decide
  have h_6 : (2 ≥ 1) := by decide
  have h_7 : (2 ≤ 3) := by decide
  have h_8 : (3 ≥ 1) := by decide
  have h_9 : (3 ≤ 3) := by decide
  have h_10 : (4 ≥ 4) := by decide
  have h_11 : (4 ≤ 6) := by decide
  have h_12 : (5 ≥ 4) := by decide
  have h_13 : (5 ≤ 6) := by decide
  have h_14 : (6 ≥ 4) := by decide
  have h_15 : (6 ≤ 6) := by decide
  have h_16 : (Nat.lcm (Nat.lcm (Nat.lcm 2 3) 4) 5 = 60) := by decide
  have h_17 : (Nat.lcm (Nat.lcm (Nat.lcm 6 7) 8) 9 = 504) := by decide
  have h_18 : (60 ≠ 504) := by decide
  have h_19 : (6 > 5) := by decide
  have h_20 : (2 ≥ 2) := by decide
  have h_21 : (2 ≤ 5) := by decide
  have h_22 : (3 ≥ 2) := by decide
  have h_23 : (3 ≤ 5) := by decide
  have h_24 : (4 ≥ 2) := by decide
  have h_25 : (4 ≤ 5) := by decide
  have h_26 : (5 ≥ 2) := by decide
  have h_27 : (5 ≤ 5) := by decide
  have h_28 : (6 ≥ 6) := by decide
  have h_29 : (6 ≤ 9) := by decide
  have h_30 : (7 ≥ 6) := by decide
  have h_31 : (7 ≤ 9) := by decide
  have h_32 : (8 ≥ 6) := by decide
  have h_33 : (8 ≤ 9) := by decide
  have h_34 : (9 ≥ 6) := by decide
  have h_35 : (9 ≤ 9) := by decide
  exact ⟨⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, ⟨h_7, h_8⟩⟩⟩⟩, ⟨⟨⟨h_9, h_10⟩, ⟨h_11, h_12⟩⟩, ⟨⟨h_13, h_14⟩, ⟨h_15, ⟨h_16, h_17⟩⟩⟩⟩⟩, ⟨⟨⟨⟨h_18, h_19⟩, ⟨h_20, h_21⟩⟩, ⟨⟨h_22, h_23⟩, ⟨h_24, ⟨h_25, h_26⟩⟩⟩⟩, ⟨⟨⟨h_27, h_28⟩, ⟨h_29, h_30⟩⟩, ⟨⟨h_31, h_32⟩, ⟨h_33, ⟨h_34, h_35⟩⟩⟩⟩⟩⟩
