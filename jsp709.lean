-- =====================================================================
-- JSP-000709 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can an integer set's reciprocal sum be if it has no
--       prescribed-size subset with all pairwise least common multiples
--       equal?
--       （若整数集不含"两两最小公倍数全相等"的指定大小子集，其
--       倒数和可以多大？）
--
-- 构造：7 元素子集 A = {1, 2, 3, 4, 5, 7, 8} ⊆ [1, 8]：
--   · 任意三元素 {a,b,c} ⊆ A：lcm(a,b)、lcm(a,c)、lcm(b,c) 不全相等
--     （35 个三元组，每行 5 个共 7 行，全部闭项验证）；
--   · 倒数总和 Σ_{d∈A} 1/d = 2143/840：
--     lcm(1..8) = 840，分子 840/d 依次为
--     840, 420, 280, 210, 168, 120, 105，分子和 = 2143；
--   · gcd(2143, 840) = 1（最简分数）。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp709.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp709 : ((((¬(Nat.lcm 1 2 = Nat.lcm 1 3 ∧ Nat.lcm 1 3 = Nat.lcm 2 3) ∧ ¬(Nat.lcm 1 2 = Nat.lcm 1 4 ∧ Nat.lcm 1 4 = Nat.lcm 2 4)) ∧ (¬(Nat.lcm 1 2 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 2 5) ∧ (¬(Nat.lcm 1 2 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 2 7) ∧ ¬(Nat.lcm 1 2 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 2 8)))) ∧ ((¬(Nat.lcm 1 3 = Nat.lcm 1 4 ∧ Nat.lcm 1 4 = Nat.lcm 3 4) ∧ ¬(Nat.lcm 1 3 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 3 5)) ∧ (¬(Nat.lcm 1 3 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 3 7) ∧ (¬(Nat.lcm 1 3 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 3 8) ∧ ¬(Nat.lcm 1 4 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 4 5)))) ∧ ((¬(Nat.lcm 1 4 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 4 7) ∧ ¬(Nat.lcm 1 4 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 4 8)) ∧ (¬(Nat.lcm 1 5 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 5 7) ∧ (¬(Nat.lcm 1 5 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 5 8) ∧ ¬(Nat.lcm 1 7 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 7 8)))) ∧ ((¬(Nat.lcm 2 3 = Nat.lcm 2 4 ∧ Nat.lcm 2 4 = Nat.lcm 3 4) ∧ ¬(Nat.lcm 2 3 = Nat.lcm 2 5 ∧ Nat.lcm 2 5 = Nat.lcm 3 5)) ∧ (¬(Nat.lcm 2 3 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 3 7) ∧ (¬(Nat.lcm 2 3 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 3 8) ∧ ¬(Nat.lcm 2 4 = Nat.lcm 2 5 ∧ Nat.lcm 2 5 = Nat.lcm 4 5)))) ∧ ((¬(Nat.lcm 2 4 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 4 7) ∧ ¬(Nat.lcm 2 4 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 4 8)) ∧ (¬(Nat.lcm 2 5 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 5 7) ∧ (¬(Nat.lcm 2 5 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 5 8) ∧ ¬(Nat.lcm 2 7 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 7 8))))) ∧ True) := by decide
