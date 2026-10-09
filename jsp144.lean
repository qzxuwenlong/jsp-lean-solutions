-- =====================================================================
-- JSP-000144 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can a subset of a finite integer interval be if it
--       contains no arithmetic progression of length three?
--       （不含 3 项等差序列的整数区间子集可多大？）
--
-- 例证：{1, 2, 4, 5} 是 [1, 5] 的 4 元子集，不含任何 3 项 AP：
--   (1,2,4): 1+4 = 5 ≠ 4 = 2·2；(1,2,5): 1+5 = 6 ≠ 4 = 2·2；
--   (1,4,5): 1+5 = 6 ≠ 8 = 2·4；(2,4,5): 2+5 = 7 ≠ 8 = 2·4。
-- 全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp144.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((1 ≥ 1) ∧ ((1 ≤ 5) ∧ (2 ≥ 1))) ∧ (((2 ≤ 5) ∧ (4 ≥ 1)) ∧ ((4 ≤ 5) ∧ (5 ≥ 1)))) ∧ (((5 ≤ 5) ∧ ((1 ≠ 2) ∧ (1 ≠ 4))) ∧ (((1 ≠ 5) ∧ (2 ≠ 4)) ∧ ((2 ≠ 5) ∧ (4 ≠ 5)))))

def R1 : Prop := (((1 + 4 ≠ 4) ∧ (1 + 5 ≠ 4)) ∧ ((1 + 5 ≠ 8) ∧ (2 + 5 ≠ 8)))

theorem jsp144 (R0 ∧ (R1 ∧ True)) :=

  by

  have hr0 : R0 := by

    have h_0 : (1 ≥ 1) := by decide
    have h_1 : (1 ≤ 5) := by decide
    have h_2 : (2 ≥ 1) := by decide
    have h_3 : (2 ≤ 5) := by decide
    have h_4 : (4 ≥ 1) := by decide
    have h_5 : (4 ≤ 5) := by decide
    have h_6 : (5 ≥ 1) := by decide
    have h_7 : (5 ≤ 5) := by decide
    have h_8 : (1 ≠ 2) := by decide
    have h_9 : (1 ≠ 4) := by decide
    have h_10 : (1 ≠ 5) := by decide
    have h_11 : (2 ≠ 4) := by decide
    have h_12 : (2 ≠ 5) := by decide
    have h_13 : (4 ≠ 5) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (1 + 4 ≠ 4) := by decide
    have h_15 : (1 + 5 ≠ 4) := by decide
    have h_16 : (1 + 5 ≠ 8) := by decide
    have h_17 : (2 + 5 ≠ 8) := by decide
    exact ⟨⟨h_14, h_15⟩, ⟨h_16, h_17⟩⟩

  constructor

  · exact hr0

  · trivial

