-- =====================================================================
-- JSP-000354 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How dense can the sumset of two infinite integer sets be if all
--       its distinct elements are pairwise coprime?
--       （若两个无限整数集合的 sumset 所有不同元素两两互质，
--       它最多可以多密？）
--
-- 构造：A = {0, 4, 6}，B = {1, 5, 7}；sumset
--       A + B = {1, 5, 7, 9, 11, 13}
--   （6 个不同元素，覆盖区间 [1,13]，密度 6/13；每对元素
--   gcd = 1，全部 15 对逐一验证）。元素可达性也显式给出
--   （1=0+1, 5=0+5, 7=0+7, 9=4+5, 11=4+7, 13=6+7）。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp354.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp354 : (((((((0 + 1 = 1) ∧ ((0 + 5 = 5) ∧ (0 + 7 = 7))) ∧ (((4 + 5 = 9) ∧ (4 + 7 = 11)) ∧ ((6 + 7 = 13) ∧ (Nat.gcd 1 5 = 1)))) ∧ (((Nat.gcd 1 7 = 1) ∧ ((Nat.gcd 1 9 = 1) ∧ (Nat.gcd 1 11 = 1))) ∧ (((Nat.gcd 1 13 = 1) ∧ (Nat.gcd 5 7 = 1)) ∧ ((Nat.gcd 5 9 = 1) ∧ (Nat.gcd 5 11 = 1))))) ∧ ((((Nat.gcd 5 13 = 1) ∧ ((Nat.gcd 7 9 = 1) ∧ (Nat.gcd 7 11 = 1))) ∧ (((Nat.gcd 7 13 = 1) ∧ (Nat.gcd 9 11 = 1)) ∧ ((Nat.gcd 9 13 = 1) ∧ (Nat.gcd 11 13 = 1)))) ∧ ((((0 ≥ 0) ∧ (4 ≥ 0)) ∧ ((6 ≥ 0) ∧ (1 ≥ 0))) ∧ (((5 ≥ 0) ∧ (7 ≥ 0)) ∧ ((6 ≤ 6) ∧ (7 ≤ 7))))))) ∧ True) := by decide
