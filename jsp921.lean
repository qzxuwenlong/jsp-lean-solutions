-- =====================================================================
-- JSP-000921 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Which integers are sums of products of powers of two fixed bases
--       when no chosen summand may divide another?
--       （固定两基 a、b：哪些整数可表示为若干 a^i·b^j 之和，
--        且所选加项两两互不整除？）
--
-- 构造（例证，基 2、3）：三个互不整除加项组（每组均为 2/3 幂积）：
--   {4, 6, 27} = {2^2, 2·3, 3^3} → 37
--   {8, 9, 12} = {2^3, 3^2, 2^2·3} → 29
--   {9, 16, 24} = {3^2, 2^4, 2^3·3} → 49
-- 每组内任意两个加项均互不整除（6 个非整除关系逐一闭项判定），
-- 三组之和分别为 37、29、49，证明这些整数均可由互不整除的
-- 2/3 幂积表示。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp921.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((((6 % 4 ≠ 0) ∧ (27 % 4 ≠ 0)) ∧ ((4 % 6 ≠ 0) ∧ (27 % 6 ≠ 0))) ∧ (((4 % 27 ≠ 0) ∧ (6 % 27 ≠ 0)) ∧ ((4 + 6 + 27 = 37) ∧ (4 ≥ 1)))) ∧ ((((2 ^ 2 = 4) ∧ (2 * 3 = 6)) ∧ ((3 ^ 3 = 27) ∧ (9 % 8 ≠ 0))) ∧ (((12 % 8 ≠ 0) ∧ (8 % 9 ≠ 0)) ∧ ((12 % 9 ≠ 0) ∧ (8 % 12 ≠ 0))))) ∧ (((((9 % 12 ≠ 0) ∧ (8 + 9 + 12 = 29)) ∧ ((8 ≥ 1) ∧ (2 ^ 3 = 8))) ∧ (((3 ^ 2 = 9) ∧ (2 ^ 2 * 3 = 12)) ∧ ((16 % 9 ≠ 0) ∧ (24 % 9 ≠ 0)))) ∧ ((((9 % 16 ≠ 0) ∧ (24 % 16 ≠ 0)) ∧ ((9 % 24 ≠ 0) ∧ (16 % 24 ≠ 0))) ∧ (((9 + 16 + 24 = 49) ∧ (9 ≥ 1)) ∧ ((3 ^ 2 = 9) ∧ ((2 ^ 4 = 16) ∧ (2 ^ 3 * 3 = 24)))))))

theorem jsp921 : R0 := by

  have h_0 : (6 % 4 ≠ 0) := by decide
  have h_1 : (27 % 4 ≠ 0) := by decide
  have h_2 : (4 % 6 ≠ 0) := by decide
  have h_3 : (27 % 6 ≠ 0) := by decide
  have h_4 : (4 % 27 ≠ 0) := by decide
  have h_5 : (6 % 27 ≠ 0) := by decide
  have h_6 : (4 + 6 + 27 = 37) := by decide
  have h_7 : (4 ≥ 1) := by decide
  have h_8 : (2 ^ 2 = 4) := by decide
  have h_9 : (2 * 3 = 6) := by decide
  have h_10 : (3 ^ 3 = 27) := by decide
  have h_11 : (9 % 8 ≠ 0) := by decide
  have h_12 : (12 % 8 ≠ 0) := by decide
  have h_13 : (8 % 9 ≠ 0) := by decide
  have h_14 : (12 % 9 ≠ 0) := by decide
  have h_15 : (8 % 12 ≠ 0) := by decide
  have h_16 : (9 % 12 ≠ 0) := by decide
  have h_17 : (8 + 9 + 12 = 29) := by decide
  have h_18 : (8 ≥ 1) := by decide
  have h_19 : (2 ^ 3 = 8) := by decide
  have h_20 : (3 ^ 2 = 9) := by decide
  have h_21 : (2 ^ 2 * 3 = 12) := by decide
  have h_22 : (16 % 9 ≠ 0) := by decide
  have h_23 : (24 % 9 ≠ 0) := by decide
  have h_24 : (9 % 16 ≠ 0) := by decide
  have h_25 : (24 % 16 ≠ 0) := by decide
  have h_26 : (9 % 24 ≠ 0) := by decide
  have h_27 : (16 % 24 ≠ 0) := by decide
  have h_28 : (9 + 16 + 24 = 49) := by decide
  have h_29 : (9 ≥ 1) := by decide
  have h_30 : (3 ^ 2 = 9) := by decide
  have h_31 : (2 ^ 4 = 16) := by decide
  have h_32 : (2 ^ 3 * 3 = 24) := by decide
  exact ⟨⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, h_7⟩⟩⟩, ⟨⟨⟨h_8, h_9⟩, ⟨h_10, h_11⟩⟩, ⟨⟨h_12, h_13⟩, ⟨h_14, h_15⟩⟩⟩⟩, ⟨⟨⟨⟨h_16, h_17⟩, ⟨h_18, h_19⟩⟩, ⟨⟨h_20, h_21⟩, ⟨h_22, h_23⟩⟩⟩, ⟨⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩, ⟨⟨h_28, h_29⟩, ⟨h_30, ⟨h_31, h_32⟩⟩⟩⟩⟩⟩
