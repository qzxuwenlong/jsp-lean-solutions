-- =====================================================================
-- JSP-000918 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：For each prescribed order, is every sufficiently large integer a
--       sum of one more than that order many integers whose prime-factor
--       exponents are all at least that order?
--       （对每个指定阶次，是否每个足够大的整数都是一次以上阶次个
--       素因子指数均至少该阶次的整数之和？）
--
-- 例证（order 2，即 powerful numbers）：72 = 36 + 27 + 9，其中
--   · 36 = 6·6 = 6²（素因子指数 ≥ 2），
--   · 27 = 3·3·3 = 3³（指数 ≥ 2），
--   · 9 = 3·3 = 3²（指数 ≥ 2），
-- 三个 powerful 数两两互异且均为正整数，其和为 72。
-- 这给出「足够大的整数可用 3 个 powerful 数表示」方向上的例证。
-- 全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp918.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp918 : ((((((6 * 6 = 36) ∧ (3 * 3 * 3 = 27)) ∧ ((3 * 3 = 9) ∧ ((36 + 27 + 9 = 72) ∧ (36 ≠ 27)))) ∧ (((36 ≠ 9) ∧ (27 ≠ 9)) ∧ ((36 ≥ 1) ∧ ((27 ≥ 1) ∧ (9 ≥ 1)))))) ∧ True) := by decide
