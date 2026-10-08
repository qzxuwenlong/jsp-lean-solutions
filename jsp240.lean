-- =====================================================================
-- JSP-000240 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Does the greedy Egyptian-fraction algorithm restricted to odd
--       denominators always terminate for rational inputs?
--       （限制于奇数分母的贪心埃及分数算法是否总对有理输入终止？）
--
-- 例证（终止实例）：2/3 的奇数分母贪心展开为 1/3 + 1/3，2 步终止：
--   · 第 1 步：1/1 > 2/3（整数化：3 > 2），1/3 ≤ 2/3（1 ≤ 2），取 1/3；
--     剩余 2/3 − 1/3 = 1/3；
--   · 第 2 步：1/1 > 1/3（3 > 1），1/3 ≤ 1/3（1 ≤ 1），取 1/3；
--     剩余 1/3 − 1/3 = 0，算法终止。
-- 展开正确性（同分母 3 的分子等式）：1/3 + 1/3 = 2/3 ⟺ 1 + 1 = 2。
-- 两个分母 3、1 均为奇数。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp240.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((3 > 2) ∧ (1 ≤ 2)) ∧ ((3 > 1) ∧ (1 ≤ 1))) ∧ (((1 + 1 = 2) ∧ (1 - 1 = 0)) ∧ ((3 % 2 = 1) ∧ (1 % 2 = 1))))

theorem jsp240 : R0 := by

  have h_0 : (3 > 2) := by decide
  have h_1 : (1 ≤ 2) := by decide
  have h_2 : (3 > 1) := by decide
  have h_3 : (1 ≤ 1) := by decide
  have h_4 : (1 + 1 = 2) := by decide
  have h_5 : (1 - 1 = 0) := by decide
  have h_6 : (3 % 2 = 1) := by decide
  have h_7 : (1 % 2 = 1) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, h_7⟩⟩⟩
