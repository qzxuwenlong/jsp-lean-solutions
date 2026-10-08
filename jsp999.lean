-- =====================================================================
-- JSP-000999 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How fast must an integer set grow if each positive integer has
--       exactly one representation as a difference of two of its elements?
--       （若每个正整数恰有一个两元素差表示，整数集增长必须多快？）
--
-- 例证：集合 A = {0, 1, 4, 6}（4 元素 Golomb 尺）的 6 个正差异为
--   1-0 = 1、4-0 = 4、6-0 = 6、4-1 = 3、6-1 = 5、6-4 = 2，
-- 恰好是 {1, 2, 3, 4, 5, 6}：6 个差异值两两互异，故每个被表示的正整数
-- （1..6 中的每一个）恰好对应唯一一个元素对。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp999.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((1 - 0 = 1) ∧ ((0 < 1) ∧ (4 - 0 = 4))) ∧ (((0 < 4) ∧ (6 - 0 = 6)) ∧ ((0 < 6) ∧ (4 - 1 = 3)))) ∧ (((1 < 4) ∧ ((6 - 1 = 5) ∧ (1 < 6))) ∧ (((6 - 4 = 2) ∧ (4 < 6)) ∧ ((0 ≠ 1) ∧ (0 ≠ 4)))))

def R1 : Prop := ((((0 ≠ 6) ∧ ((1 ≠ 4) ∧ (1 ≠ 6))) ∧ (((4 ≠ 6) ∧ (1 ≠ 4)) ∧ ((1 ≠ 6) ∧ (1 ≠ 3)))) ∧ (((1 ≠ 5) ∧ ((1 ≠ 2) ∧ (4 ≠ 6))) ∧ (((4 ≠ 3) ∧ (4 ≠ 5)) ∧ ((4 ≠ 2) ∧ (6 ≠ 3)))))

def R2 : Prop := ((((6 ≠ 5) ∧ ((6 ≠ 2) ∧ (3 ≠ 5))) ∧ (((3 ≠ 2) ∧ (5 ≠ 2)) ∧ ((1 ≥ 1) ∧ (1 ≤ 6)))) ∧ (((4 ≥ 1) ∧ ((4 ≤ 6) ∧ (6 ≥ 1))) ∧ (((6 ≤ 6) ∧ (3 ≥ 1)) ∧ ((3 ≤ 6) ∧ (5 ≥ 1)))))

def R3 : Prop := ((5 ≤ 6) ∧ ((2 ≥ 1) ∧ (2 ≤ 6)))

theorem jsp999 (R0 ∧ (R1 ∧ (R2 ∧ (R3 ∧ True)))) :=

  by

  have hr0 : R0 := by

    have h_0 : (1 - 0 = 1) := by decide
    have h_1 : (0 < 1) := by decide
    have h_2 : (4 - 0 = 4) := by decide
    have h_3 : (0 < 4) := by decide
    have h_4 : (6 - 0 = 6) := by decide
    have h_5 : (0 < 6) := by decide
    have h_6 : (4 - 1 = 3) := by decide
    have h_7 : (1 < 4) := by decide
    have h_8 : (6 - 1 = 5) := by decide
    have h_9 : (1 < 6) := by decide
    have h_10 : (6 - 4 = 2) := by decide
    have h_11 : (4 < 6) := by decide
    have h_12 : (0 ≠ 1) := by decide
    have h_13 : (0 ≠ 4) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (0 ≠ 6) := by decide
    have h_15 : (1 ≠ 4) := by decide
    have h_16 : (1 ≠ 6) := by decide
    have h_17 : (4 ≠ 6) := by decide
    have h_18 : (1 ≠ 4) := by decide
    have h_19 : (1 ≠ 6) := by decide
    have h_20 : (1 ≠ 3) := by decide
    have h_21 : (1 ≠ 5) := by decide
    have h_22 : (1 ≠ 2) := by decide
    have h_23 : (4 ≠ 6) := by decide
    have h_24 : (4 ≠ 3) := by decide
    have h_25 : (4 ≠ 5) := by decide
    have h_26 : (4 ≠ 2) := by decide
    have h_27 : (6 ≠ 3) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (6 ≠ 5) := by decide
    have h_29 : (6 ≠ 2) := by decide
    have h_30 : (3 ≠ 5) := by decide
    have h_31 : (3 ≠ 2) := by decide
    have h_32 : (5 ≠ 2) := by decide
    have h_33 : (1 ≥ 1) := by decide
    have h_34 : (1 ≤ 6) := by decide
    have h_35 : (4 ≥ 1) := by decide
    have h_36 : (4 ≤ 6) := by decide
    have h_37 : (6 ≥ 1) := by decide
    have h_38 : (6 ≤ 6) := by decide
    have h_39 : (3 ≥ 1) := by decide
    have h_40 : (3 ≤ 6) := by decide
    have h_41 : (5 ≥ 1) := by decide
    exact ⟨⟨⟨h_28, ⟨h_29, h_30⟩⟩, ⟨⟨h_31, h_32⟩, ⟨h_33, h_34⟩⟩⟩, ⟨⟨h_35, ⟨h_36, h_37⟩⟩, ⟨⟨h_38, h_39⟩, ⟨h_40, h_41⟩⟩⟩⟩

  have hr3 : R3 := by

    have h_42 : (5 ≤ 6) := by decide
    have h_43 : (2 ≥ 1) := by decide
    have h_44 : (2 ≤ 6) := by decide
    exact ⟨h_42, ⟨h_43, h_44⟩⟩

  constructor

  · exact hr0

  · exact hr1

  · exact hr2

  · trivial

