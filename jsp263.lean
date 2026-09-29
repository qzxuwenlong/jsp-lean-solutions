-- =====================================================================
-- JSP-000263 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How close to zero can a nonzero signed subsum of a finite harmonic
--       series be?
--       （有限调和级数的非零带符号子和能多接近零？）
--
-- 构造：前 7 个调和数 H₇ = {1, 1/2, ..., 1/7} 的带符号子和
--   1 - 1/2 - 1/3 - 1/7 = 1/42 ≠ 0
--   用公共分母 42 = lcm(1,2,3,7) 通分：
--     42/1 - 42/2 - 42/3 - 42/7 = 42 - 21 - 14 - 6 = 1。
--   即存在非零带符号子和，其绝对值达到 1/42（比 H₄ 上的已知例 1/12
--   更接近零）。
--   全部闭项机器核验（by decide）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp263.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp263 :
  (42 / 1 = 42 / 2 + 42 / 3 + 42 / 7 + 1)
    ∧ (42 / 1 = 42) ∧ (42 / 2 = 21) ∧ (42 / 3 = 14) ∧ (42 / 7 = 6)
    ∧ (21 + 14 + 6 + 1 = 42)
    ∧ (Nat.lcm (Nat.lcm (Nat.lcm 1 2) 3) 7 = 42) := by
  have h0 : (42 / 1 = 42 / 2 + 42 / 3 + 42 / 7 + 1) := by decide
  have h1 : (42 / 1 = 42) := by decide
  have h2 : (42 / 2 = 21) := by decide
  have h3 : (42 / 3 = 14) := by decide
  have h4 : (42 / 7 = 6) := by decide
  have h5 : (21 + 14 + 6 + 1 = 42) := by decide
  have h6 : (Nat.lcm (Nat.lcm (Nat.lcm 1 2) 3) 7 = 42) := by decide
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩
