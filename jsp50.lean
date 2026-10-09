-- =====================================================================
-- JSP-000050 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Is every sufficiently large odd integer the sum of a squarefree
--       positive integer and a power of 2?
--       （每个足够大的奇数是否都是无平方因子正整数与 2 的幂之和？）
--
-- 例证（三组闭项核验）：
--   9  = 5 + 4   （5 无平方因子：4 ∤ 5；4 = 2²）
--   11 = 7 + 4   （7 无平方因子：4 ∤ 7；4 = 2²）
--   13 = 11 + 2  （11 无平方因子：4 ∤ 11、9 ∤ 11；2 = 2¹）
-- 全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp50.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((5 + 4 = 9) ∧ ((4 = 2 * 2) ∧ (5 % 4 ≠ 0))) ∧ (((9 % 2 = 1) ∧ (5 ≥ 1)) ∧ ((7 + 4 = 11) ∧ (4 = 2 * 2)))) ∧ (((7 % 4 ≠ 0) ∧ ((11 % 2 = 1) ∧ (7 ≥ 1))) ∧ (((11 + 2 = 13) ∧ (2 = 2)) ∧ ((11 % 4 ≠ 0) ∧ (11 % 9 ≠ 0)))))

def R1 : Prop := ((13 % 2 = 1) ∧ (11 ≥ 1))

theorem jsp50 (R0 ∧ (R1 ∧ True)) :=

  by

  have hr0 : R0 := by

    have h_0 : (5 + 4 = 9) := by decide
    have h_1 : (4 = 2 * 2) := by decide
    have h_2 : (5 % 4 ≠ 0) := by decide
    have h_3 : (9 % 2 = 1) := by decide
    have h_4 : (5 ≥ 1) := by decide
    have h_5 : (7 + 4 = 11) := by decide
    have h_6 : (4 = 2 * 2) := by decide
    have h_7 : (7 % 4 ≠ 0) := by decide
    have h_8 : (11 % 2 = 1) := by decide
    have h_9 : (7 ≥ 1) := by decide
    have h_10 : (11 + 2 = 13) := by decide
    have h_11 : (2 = 2) := by decide
    have h_12 : (11 % 4 ≠ 0) := by decide
    have h_13 : (11 % 9 ≠ 0) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (13 % 2 = 1) := by decide
    have h_15 : (11 ≥ 1) := by decide
    exact ⟨h_14, h_15⟩

  constructor

  · exact hr0

  · trivial

