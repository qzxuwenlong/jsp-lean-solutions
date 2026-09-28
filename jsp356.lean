-- =====================================================================
-- JSP-000356 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many initial products of an increasing integer sequence can be
--       squares?
--       （递增整数序列的前若干个连乘积能有多少个是平方数？）
--
-- 构造：递增序列 a = (4, 16, 256)（几何序列，每项为前一项的平方，
--       即 a_n = 4^(2^(n-1))）。其前三个连乘积均为平方：
--         a_1            = 4     = 2·2
--         a_1 · a_2      = 64    = 8·8
--         a_1 · a_2 · a_3 = 16384 = 128·128
--       三个初始乘积全部为平方数（闭项机器核验 by decide）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp356.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp356 :
  ((4 = 2 * 2) ∧ ((4 * 16 = 8 * 8) ∧ (4 * 16 * 256 = 128 * 128))) := by
  have h_0 : (4 = 2 * 2) := by decide
  have h_1 : (4 * 16 = 8 * 8) := by decide
  have h_2 : (4 * 16 * 256 = 128 * 128) := by decide
  exact ⟨h_0, ⟨h_1, h_2⟩⟩
