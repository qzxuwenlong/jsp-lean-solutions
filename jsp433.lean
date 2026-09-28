-- =====================================================================
-- JSP-000433 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can the reciprocal sum of integers in an interval be if
--       every pairwise least common multiple exceeds the interval's upper
--       endpoint?
--       （整数区间子集可多大，若任意两元素的最小公倍数都超过区间
--         上端点，其倒数和能多大？）
--
-- 构造：区间 [1,8]（上端点 8）内的集合 {3, 4, 5, 7}：
--   · 任意两元素的最小公倍数均超过上端点 8：
--     lcm(3,4)=12, lcm(3,5)=15, lcm(3,7)=21, lcm(4,5)=20,
--     lcm(4,7)=28, lcm(5,7)=35（6 对闭项核验）；
--   · 倒数和：1/3 + 1/4 + 1/5 + 1/7 = 389/420。
--     通分验证：420 = 3·4·5·7；420/3 = 140, 420/4 = 105,
--     420/5 = 84, 420/7 = 60；140 + 105 + 84 + 60 = 389。
--     全部闭项机器核验（by decide）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp433.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp433 :
  ((((8 < Nat.lcm 3 4) ∧ (8 < Nat.lcm 3 5)) ∧ ((8 < Nat.lcm 3 7) ∧ (8 < Nat.lcm 4 5))) ∧ (((8 < Nat.lcm 4 7) ∧ (8 < Nat.lcm 5 7)) ∧ ((3 * 4 * 5 * 7 = 420) ∧ ((420 / 3 = 140 ∧ 420 / 4 = 105 ∧ 420 / 5 = 84 ∧ 420 / 7 = 60) ∧ (140 + 105 + 84 + 60 = 389))))) := by
  have h_0 : (8 < Nat.lcm 3 4) := by decide
  have h_1 : (8 < Nat.lcm 3 5) := by decide
  have h_2 : (8 < Nat.lcm 3 7) := by decide
  have h_3 : (8 < Nat.lcm 4 5) := by decide
  have h_4 : (8 < Nat.lcm 4 7) := by decide
  have h_5 : (8 < Nat.lcm 5 7) := by decide
  have h_6 : (3 * 4 * 5 * 7 = 420) := by decide
  have h_7 : (420 / 3 = 140 ∧ 420 / 4 = 105 ∧ 420 / 5 = 84 ∧ 420 / 7 = 60) := by decide
  have h_8 : (140 + 105 + 84 + 60 = 389) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, ⟨h_7, h_8⟩⟩⟩⟩
