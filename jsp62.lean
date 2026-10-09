-- =====================================================================
-- JSP-000062 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can a set with distinct two-element sums in a finite
--       integer interval be, and how large can the corresponding
--       differences be?
--       （有限整数区间中两两和互异的集合可多大？）
--
-- 例证：{1, 2, 5, 10} 是 [1, 10] 的 4 元 Sidon 集：其 6 个两两和
--   1+2 = 3、1+5 = 6、1+10 = 11、2+5 = 7、2+10 = 12、5+10 = 15
-- 两两互异。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp62.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((1 ≥ 1) ∧ ((1 ≤ 10) ∧ (2 ≥ 1))) ∧ (((2 ≤ 10) ∧ (5 ≥ 1)) ∧ ((5 ≤ 10) ∧ (10 ≥ 1)))) ∧ (((10 ≤ 10) ∧ ((1 ≠ 2) ∧ (1 ≠ 5))) ∧ (((1 ≠ 10) ∧ (2 ≠ 5)) ∧ ((2 ≠ 10) ∧ (5 ≠ 10)))))

def R1 : Prop := ((((3 ≠ 6) ∧ ((3 ≠ 11) ∧ (3 ≠ 7))) ∧ (((3 ≠ 12) ∧ (3 ≠ 15)) ∧ ((6 ≠ 11) ∧ (6 ≠ 7)))) ∧ (((6 ≠ 12) ∧ ((6 ≠ 15) ∧ (11 ≠ 7))) ∧ (((11 ≠ 12) ∧ (11 ≠ 15)) ∧ ((7 ≠ 12) ∧ (7 ≠ 15)))))

def R2 : Prop := (12 ≠ 15)

theorem jsp62 (R0 ∧ (R1 ∧ (R2 ∧ True))) :=

  by

  have hr0 : R0 := by

    have h_0 : (1 ≥ 1) := by decide
    have h_1 : (1 ≤ 10) := by decide
    have h_2 : (2 ≥ 1) := by decide
    have h_3 : (2 ≤ 10) := by decide
    have h_4 : (5 ≥ 1) := by decide
    have h_5 : (5 ≤ 10) := by decide
    have h_6 : (10 ≥ 1) := by decide
    have h_7 : (10 ≤ 10) := by decide
    have h_8 : (1 ≠ 2) := by decide
    have h_9 : (1 ≠ 5) := by decide
    have h_10 : (1 ≠ 10) := by decide
    have h_11 : (2 ≠ 5) := by decide
    have h_12 : (2 ≠ 10) := by decide
    have h_13 : (5 ≠ 10) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (3 ≠ 6) := by decide
    have h_15 : (3 ≠ 11) := by decide
    have h_16 : (3 ≠ 7) := by decide
    have h_17 : (3 ≠ 12) := by decide
    have h_18 : (3 ≠ 15) := by decide
    have h_19 : (6 ≠ 11) := by decide
    have h_20 : (6 ≠ 7) := by decide
    have h_21 : (6 ≠ 12) := by decide
    have h_22 : (6 ≠ 15) := by decide
    have h_23 : (11 ≠ 7) := by decide
    have h_24 : (11 ≠ 12) := by decide
    have h_25 : (11 ≠ 15) := by decide
    have h_26 : (7 ≠ 12) := by decide
    have h_27 : (7 ≠ 15) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (12 ≠ 15) := by decide
    exact h_28

  constructor

  · exact hr0

  · exact hr1

  · trivial

