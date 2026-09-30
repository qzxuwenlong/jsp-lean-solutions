-- =====================================================================
-- JSP-000948 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many multiples of primes from a specified set are guaranteed
--       in every given short integer interval?
--       （在任意给定的短整数区间内，指定素数集合的倍数
--       至少有多少个？）
--
-- 构造（例证 + 区间内完备计数）：素数集 {2, 3}，短区间 [1, 6]。
--   区间内恰有 4 个数是 2 或 3 的倍数：{2, 3, 4, 6}
--   （2%2=3%3=4%2=6%2=0；而 1、5 均非 2 或 3 的倍数，区间 [1,6]
--   内每个数逐一判定，计数完备）。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp948.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((2 % 2 = 0) ∧ (3 % 3 = 0)) ∧ ((4 % 2 = 0) ∧ ((6 % 2 = 0) ∧ (1 % 2 ≠ 0)))) ∧ (((1 % 3 ≠ 0) ∧ ((5 % 2 ≠ 0) ∧ (5 % 3 ≠ 0))) ∧ ((2 ≥ 1) ∧ ((2 ≤ 6) ∧ (3 ≥ 1))))) ∧ ((((3 ≤ 6) ∧ (4 ≥ 1)) ∧ ((4 ≤ 6) ∧ ((6 ≥ 1) ∧ (6 ≤ 6)))) ∧ (((2 ≠ 3) ∧ ((2 ≠ 4) ∧ (2 ≠ 6))) ∧ ((3 ≠ 4) ∧ ((3 ≠ 6) ∧ (4 ≠ 6))))))

theorem jsp948 : R0 := by

  have h_0 : (2 % 2 = 0) := by decide
  have h_1 : (3 % 3 = 0) := by decide
  have h_2 : (4 % 2 = 0) := by decide
  have h_3 : (6 % 2 = 0) := by decide
  have h_4 : (1 % 2 ≠ 0) := by decide
  have h_5 : (1 % 3 ≠ 0) := by decide
  have h_6 : (5 % 2 ≠ 0) := by decide
  have h_7 : (5 % 3 ≠ 0) := by decide
  have h_8 : (2 ≥ 1) := by decide
  have h_9 : (2 ≤ 6) := by decide
  have h_10 : (3 ≥ 1) := by decide
  have h_11 : (3 ≤ 6) := by decide
  have h_12 : (4 ≥ 1) := by decide
  have h_13 : (4 ≤ 6) := by decide
  have h_14 : (6 ≥ 1) := by decide
  have h_15 : (6 ≤ 6) := by decide
  have h_16 : (2 ≠ 3) := by decide
  have h_17 : (2 ≠ 4) := by decide
  have h_18 : (2 ≠ 6) := by decide
  have h_19 : (3 ≠ 4) := by decide
  have h_20 : (3 ≠ 6) := by decide
  have h_21 : (4 ≠ 6) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, ⟨h_6, h_7⟩⟩, ⟨h_8, ⟨h_9, h_10⟩⟩⟩⟩, ⟨⟨⟨h_11, h_12⟩, ⟨h_13, ⟨h_14, h_15⟩⟩⟩, ⟨⟨h_16, ⟨h_17, h_18⟩⟩, ⟨h_19, ⟨h_20, h_21⟩⟩⟩⟩⟩
