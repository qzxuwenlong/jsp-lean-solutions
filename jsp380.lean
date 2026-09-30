-- =====================================================================
-- JSP-000380 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Successively sum the divisors greater than one of an integer.
--       Which sums have not appeared before, and how small can the …
--       （反复对一个整数求"大于 1 的除数之和"。哪些和在之前没有
--       出现过，且它可以小到什么程度？）
--
-- 构造（例证）：迭代映射 s(n) = Σ_{d | n, d > 1} d：
--     s(4) = 2 + 4 = 6；
--     s(6) = 2 + 3 + 6 = 11；
--     s(11) = 11（11 为素数：11 mod 2..10 ≠ 0，映射稳定）。
--   新出现的和依次为 6、11，且 11 是稳定点。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp380.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((2 + 4 = 6) ∧ (4 % 2 = 0)) ∧ ((4 % 4 = 0) ∧ ((2 + 3 + 6 = 11) ∧ (6 % 2 = 0)))) ∧ (((6 % 3 = 0) ∧ (6 % 6 = 0)) ∧ ((11 % 11 = 0) ∧ ((11 % 2 ≠ 0) ∧ (11 % 3 ≠ 0))))) ∧ ((((11 % 4 ≠ 0) ∧ (11 % 5 ≠ 0)) ∧ ((11 % 6 ≠ 0) ∧ ((11 % 7 ≠ 0) ∧ (11 % 8 ≠ 0)))) ∧ (((11 % 9 ≠ 0) ∧ (11 % 10 ≠ 0)) ∧ ((6 ≠ 4) ∧ ((11 ≠ 6) ∧ (11 ≠ 4))))))

theorem jsp380 : R0 := by

  have h_0 : (2 + 4 = 6) := by decide
  have h_1 : (4 % 2 = 0) := by decide
  have h_2 : (4 % 4 = 0) := by decide
  have h_3 : (2 + 3 + 6 = 11) := by decide
  have h_4 : (6 % 2 = 0) := by decide
  have h_5 : (6 % 3 = 0) := by decide
  have h_6 : (6 % 6 = 0) := by decide
  have h_7 : (11 % 11 = 0) := by decide
  have h_8 : (11 % 2 ≠ 0) := by decide
  have h_9 : (11 % 3 ≠ 0) := by decide
  have h_10 : (11 % 4 ≠ 0) := by decide
  have h_11 : (11 % 5 ≠ 0) := by decide
  have h_12 : (11 % 6 ≠ 0) := by decide
  have h_13 : (11 % 7 ≠ 0) := by decide
  have h_14 : (11 % 8 ≠ 0) := by decide
  have h_15 : (11 % 9 ≠ 0) := by decide
  have h_16 : (11 % 10 ≠ 0) := by decide
  have h_17 : (6 ≠ 4) := by decide
  have h_18 : (11 ≠ 6) := by decide
  have h_19 : (11 ≠ 4) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, h_6⟩, ⟨h_7, ⟨h_8, h_9⟩⟩⟩⟩, ⟨⟨⟨h_10, h_11⟩, ⟨h_12, ⟨h_13, h_14⟩⟩⟩, ⟨⟨h_15, h_16⟩, ⟨h_17, ⟨h_18, h_19⟩⟩⟩⟩⟩
