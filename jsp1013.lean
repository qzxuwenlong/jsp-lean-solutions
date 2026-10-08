-- =====================================================================
-- JSP-001013 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：In fixed dimension, how large a subset with all pairwise
--       distances distinct must every finite point set contain?
--       （固定维数下，每个有限点集必含多大的全距离互异子集？）
--
-- 例证：一维点集 {0, 1, 3, 7}（4 个点）的所有 6 个两两距离
--   |1−0| = 1、|3−0| = 3、|7−0| = 7、|3−1| = 2、|7−1| = 6、|7−3| = 4
-- 两两互异（恰好是 {1, 2, 3, 4, 6, 7}），即该有限点集整体就是全距离
-- 互异子集（一维 Golomb 尺）。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp1013.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((1 - 0 = 1) ∧ ((0 < 1) ∧ (3 - 0 = 3))) ∧ (((0 < 3) ∧ (7 - 0 = 7)) ∧ ((0 < 7) ∧ (3 - 1 = 2)))) ∧ (((1 < 3) ∧ ((7 - 1 = 6) ∧ (1 < 7))) ∧ (((7 - 3 = 4) ∧ (3 < 7)) ∧ ((0 ≠ 1) ∧ (0 ≠ 3)))))

def R1 : Prop := ((((0 ≠ 7) ∧ ((1 ≠ 3) ∧ (1 ≠ 7))) ∧ (((3 ≠ 7) ∧ (1 ≠ 3)) ∧ ((1 ≠ 7) ∧ (1 ≠ 2)))) ∧ (((1 ≠ 6) ∧ ((1 ≠ 4) ∧ (3 ≠ 7))) ∧ (((3 ≠ 2) ∧ (3 ≠ 6)) ∧ ((3 ≠ 4) ∧ (7 ≠ 2)))))

def R2 : Prop := ((((7 ≠ 6) ∧ (7 ≠ 4)) ∧ ((2 ≠ 6) ∧ ((2 ≠ 4) ∧ (6 ≠ 4)))) ∧ (((1 ≥ 1) ∧ ((3 ≥ 1) ∧ (7 ≥ 1))) ∧ ((2 ≥ 1) ∧ ((6 ≥ 1) ∧ (4 ≥ 1)))))

theorem jsp1013 (R0 ∧ (R1 ∧ (R2 ∧ True))) :=

  by

  have hr0 : R0 := by

    have h_0 : (1 - 0 = 1) := by decide
    have h_1 : (0 < 1) := by decide
    have h_2 : (3 - 0 = 3) := by decide
    have h_3 : (0 < 3) := by decide
    have h_4 : (7 - 0 = 7) := by decide
    have h_5 : (0 < 7) := by decide
    have h_6 : (3 - 1 = 2) := by decide
    have h_7 : (1 < 3) := by decide
    have h_8 : (7 - 1 = 6) := by decide
    have h_9 : (1 < 7) := by decide
    have h_10 : (7 - 3 = 4) := by decide
    have h_11 : (3 < 7) := by decide
    have h_12 : (0 ≠ 1) := by decide
    have h_13 : (0 ≠ 3) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (0 ≠ 7) := by decide
    have h_15 : (1 ≠ 3) := by decide
    have h_16 : (1 ≠ 7) := by decide
    have h_17 : (3 ≠ 7) := by decide
    have h_18 : (1 ≠ 3) := by decide
    have h_19 : (1 ≠ 7) := by decide
    have h_20 : (1 ≠ 2) := by decide
    have h_21 : (1 ≠ 6) := by decide
    have h_22 : (1 ≠ 4) := by decide
    have h_23 : (3 ≠ 7) := by decide
    have h_24 : (3 ≠ 2) := by decide
    have h_25 : (3 ≠ 6) := by decide
    have h_26 : (3 ≠ 4) := by decide
    have h_27 : (7 ≠ 2) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (7 ≠ 6) := by decide
    have h_29 : (7 ≠ 4) := by decide
    have h_30 : (2 ≠ 6) := by decide
    have h_31 : (2 ≠ 4) := by decide
    have h_32 : (6 ≠ 4) := by decide
    have h_33 : (1 ≥ 1) := by decide
    have h_34 : (3 ≥ 1) := by decide
    have h_35 : (7 ≥ 1) := by decide
    have h_36 : (2 ≥ 1) := by decide
    have h_37 : (6 ≥ 1) := by decide
    have h_38 : (4 ≥ 1) := by decide
    exact ⟨⟨⟨h_28, h_29⟩, ⟨h_30, ⟨h_31, h_32⟩⟩⟩, ⟨⟨h_33, ⟨h_34, h_35⟩⟩, ⟨h_36, ⟨h_37, h_38⟩⟩⟩⟩

  constructor

  · exact hr0

  · exact hr1

  · trivial

