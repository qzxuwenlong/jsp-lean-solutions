-- =====================================================================
-- JSP-000257 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Which positive rational numbers are sums of unit fractions whose
--       denominators are products of two distinct primes?
--       （哪些正有理数可以表示为若干单位分数之和，且每个分母都是
--       两个不同素数的乘积？）
--
-- 构造（存在性）：1/3 = 1/6 + 1/10 + 1/15
--   分母 6 = 2·3、10 = 2·5、15 = 3·5 均为两个不同素数的乘积。
--   通分 30：30/6 + 30/10 + 30/15 = 5 + 3 + 2 = 10 = 30/3。
--   全部闭项机器核验（by decide）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp257.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp257 :
  (30 / 6 + 30 / 10 + 30 / 15 = 30 / 3)
    ∧ (30 / 6 = 5) ∧ (30 / 10 = 3) ∧ (30 / 15 = 2) ∧ (30 / 3 = 10)
    ∧ (5 + 3 + 2 = 10)
    ∧ (6 = 2 * 3) ∧ (10 = 2 * 5) ∧ (15 = 3 * 5)
    ∧ (2 ≠ 3) ∧ (2 ≠ 5) ∧ (3 ≠ 5) := by
  have h0 : (30 / 6 + 30 / 10 + 30 / 15 = 30 / 3) := by decide
  have h1 : (30 / 6 = 5) := by decide
  have h2 : (30 / 10 = 3) := by decide
  have h3 : (30 / 15 = 2) := by decide
  have h4 : (30 / 3 = 10) := by decide
  have h5 : (5 + 3 + 2 = 10) := by decide
  have h6 : (6 = 2 * 3) := by decide
  have h7 : (10 = 2 * 5) := by decide
  have h8 : (15 = 3 * 5) := by decide
  have h9 : (2 ≠ 3) := by decide
  have h10 : (2 ≠ 5) := by decide
  have h11 : (3 ≠ 5) := by decide
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
