-- =====================================================================
-- JSP-000167 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：sparse ruler problem
--       例证：6 标记稀疏尺 {0, 1, 2, 6, 10, 13} 覆盖长度 13 的
--       全部距离 1..13：
--   1 = 1−0、2 = 2−0、3 = 13−10、4 = 6−2、5 = 6−1、6 = 6−0、
--   7 = 13−6、8 = 10−2、9 = 10−1、10 = 10−0、11 = 13−2、
--   12 = 13−1、13 = 13−0。
--       全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp167.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((0 ≠ 1) ∧ ((0 ≠ 2) ∧ (0 ≠ 6))) ∧ (((0 ≠ 10) ∧ (0 ≠ 13)) ∧ ((1 ≠ 2) ∧ (1 ≠ 6)))) ∧ (((1 ≠ 10) ∧ ((1 ≠ 13) ∧ (2 ≠ 6))) ∧ (((2 ≠ 10) ∧ (2 ≠ 13)) ∧ ((6 ≠ 10) ∧ (6 ≠ 13)))))

def R1 : Prop := ((((10 ≠ 13) ∧ ((0 ≥ 0) ∧ (0 ≤ 13))) ∧ (((1 ≥ 0) ∧ (1 ≤ 13)) ∧ ((2 ≥ 0) ∧ (2 ≤ 13)))) ∧ (((6 ≥ 0) ∧ ((6 ≤ 13) ∧ (10 ≥ 0))) ∧ (((10 ≤ 13) ∧ (13 ≥ 0)) ∧ ((13 ≤ 13) ∧ (1 - 0 = 1)))))

def R2 : Prop := ((((2 - 0 = 2) ∧ ((13 - 10 = 3) ∧ (6 - 2 = 4))) ∧ ((6 - 1 = 5) ∧ ((6 - 0 = 6) ∧ (13 - 6 = 7)))) ∧ (((10 - 2 = 8) ∧ ((10 - 1 = 9) ∧ (10 - 0 = 10))) ∧ ((13 - 2 = 11) ∧ ((13 - 1 = 12) ∧ (13 - 0 = 13)))))

theorem jsp167 (R0 ∧ (R1 ∧ (R2 ∧ True))) :=

  by

  have hr0 : R0 := by

    have h_0 : (0 ≠ 1) := by decide
    have h_1 : (0 ≠ 2) := by decide
    have h_2 : (0 ≠ 6) := by decide
    have h_3 : (0 ≠ 10) := by decide
    have h_4 : (0 ≠ 13) := by decide
    have h_5 : (1 ≠ 2) := by decide
    have h_6 : (1 ≠ 6) := by decide
    have h_7 : (1 ≠ 10) := by decide
    have h_8 : (1 ≠ 13) := by decide
    have h_9 : (2 ≠ 6) := by decide
    have h_10 : (2 ≠ 10) := by decide
    have h_11 : (2 ≠ 13) := by decide
    have h_12 : (6 ≠ 10) := by decide
    have h_13 : (6 ≠ 13) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (10 ≠ 13) := by decide
    have h_15 : (0 ≥ 0) := by decide
    have h_16 : (0 ≤ 13) := by decide
    have h_17 : (1 ≥ 0) := by decide
    have h_18 : (1 ≤ 13) := by decide
    have h_19 : (2 ≥ 0) := by decide
    have h_20 : (2 ≤ 13) := by decide
    have h_21 : (6 ≥ 0) := by decide
    have h_22 : (6 ≤ 13) := by decide
    have h_23 : (10 ≥ 0) := by decide
    have h_24 : (10 ≤ 13) := by decide
    have h_25 : (13 ≥ 0) := by decide
    have h_26 : (13 ≤ 13) := by decide
    have h_27 : (1 - 0 = 1) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (2 - 0 = 2) := by decide
    have h_29 : (13 - 10 = 3) := by decide
    have h_30 : (6 - 2 = 4) := by decide
    have h_31 : (6 - 1 = 5) := by decide
    have h_32 : (6 - 0 = 6) := by decide
    have h_33 : (13 - 6 = 7) := by decide
    have h_34 : (10 - 2 = 8) := by decide
    have h_35 : (10 - 1 = 9) := by decide
    have h_36 : (10 - 0 = 10) := by decide
    have h_37 : (13 - 2 = 11) := by decide
    have h_38 : (13 - 1 = 12) := by decide
    have h_39 : (13 - 0 = 13) := by decide
    exact ⟨⟨⟨h_28, ⟨h_29, h_30⟩⟩, ⟨h_31, ⟨h_32, h_33⟩⟩⟩, ⟨⟨h_34, ⟨h_35, h_36⟩⟩, ⟨h_37, ⟨h_38, h_39⟩⟩⟩⟩

  constructor

  · exact hr0

  · exact hr1

  · trivial

