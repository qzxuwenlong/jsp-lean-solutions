-- =====================================================================
-- JSP-000634 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large a Sidon set can be chosen among squares in a
--       prescribed range?
--       （指定范围内的平方中可选多大的 Sidon 集？）
--
-- 例证：{1, 4, 9, 16} = {1², 2², 3², 4²} 是 [1, 16] 内的 4 元平方
-- Sidon 集：其 6 个两两和
--   1+4 = 5、1+9 = 10、1+16 = 17、4+9 = 13、4+16 = 20、9+16 = 25
-- 两两互异。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp634.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((1 * 1 = 1) ∧ ((2 * 2 = 4) ∧ (3 * 3 = 9))) ∧ (((4 * 4 = 16) ∧ (1 ≥ 1)) ∧ ((1 ≤ 16) ∧ (4 ≥ 1)))) ∧ (((4 ≤ 16) ∧ ((9 ≥ 1) ∧ (9 ≤ 16))) ∧ (((16 ≥ 1) ∧ (16 ≤ 16)) ∧ ((1 ≠ 4) ∧ (1 ≠ 9)))))

def R1 : Prop := ((((1 ≠ 16) ∧ ((4 ≠ 9) ∧ (4 ≠ 16))) ∧ (((9 ≠ 16) ∧ (5 ≠ 10)) ∧ ((5 ≠ 17) ∧ (5 ≠ 13)))) ∧ (((5 ≠ 20) ∧ ((5 ≠ 25) ∧ (10 ≠ 17))) ∧ (((10 ≠ 13) ∧ (10 ≠ 20)) ∧ ((10 ≠ 25) ∧ (17 ≠ 13)))))

def R2 : Prop := (((17 ≠ 20) ∧ (17 ≠ 25)) ∧ ((13 ≠ 20) ∧ ((13 ≠ 25) ∧ (20 ≠ 25))))

theorem jsp634 (R0 ∧ (R1 ∧ (R2 ∧ True))) :=

  by

  have hr0 : R0 := by

    have h_0 : (1 * 1 = 1) := by decide
    have h_1 : (2 * 2 = 4) := by decide
    have h_2 : (3 * 3 = 9) := by decide
    have h_3 : (4 * 4 = 16) := by decide
    have h_4 : (1 ≥ 1) := by decide
    have h_5 : (1 ≤ 16) := by decide
    have h_6 : (4 ≥ 1) := by decide
    have h_7 : (4 ≤ 16) := by decide
    have h_8 : (9 ≥ 1) := by decide
    have h_9 : (9 ≤ 16) := by decide
    have h_10 : (16 ≥ 1) := by decide
    have h_11 : (16 ≤ 16) := by decide
    have h_12 : (1 ≠ 4) := by decide
    have h_13 : (1 ≠ 9) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (1 ≠ 16) := by decide
    have h_15 : (4 ≠ 9) := by decide
    have h_16 : (4 ≠ 16) := by decide
    have h_17 : (9 ≠ 16) := by decide
    have h_18 : (5 ≠ 10) := by decide
    have h_19 : (5 ≠ 17) := by decide
    have h_20 : (5 ≠ 13) := by decide
    have h_21 : (5 ≠ 20) := by decide
    have h_22 : (5 ≠ 25) := by decide
    have h_23 : (10 ≠ 17) := by decide
    have h_24 : (10 ≠ 13) := by decide
    have h_25 : (10 ≠ 20) := by decide
    have h_26 : (10 ≠ 25) := by decide
    have h_27 : (17 ≠ 13) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (17 ≠ 20) := by decide
    have h_29 : (17 ≠ 25) := by decide
    have h_30 : (13 ≠ 20) := by decide
    have h_31 : (13 ≠ 25) := by decide
    have h_32 : (20 ≠ 25) := by decide
    exact ⟨⟨h_28, h_29⟩, ⟨h_30, ⟨h_31, h_32⟩⟩⟩

  constructor

  · exact hr0

  · exact hr1

  · trivial

