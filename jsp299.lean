-- =====================================================================
-- JSP-000299 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can a subset of a finite integer range be if none of
--       its subset sums equals a prescribed target?
--       （有限整数区间的子集，若其任何子集和都不等于指定目标，可多大？）
--
-- 例证：A = {2, 4, 6, 8, 10} 是 [1, 10] 的 5 元子集，指定目标 11：
-- 全部 31 个非空子集和均为偶数（元素全偶），故没有任何子集和等于
-- 奇数 11。全部 31 个子集和逐一枚举，闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp299.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((2 ≥ 1) ∧ ((2 ≤ 10) ∧ (2 % 2 = 0))) ∧ (((4 ≥ 1) ∧ (4 ≤ 10)) ∧ ((4 % 2 = 0) ∧ (6 ≥ 1)))) ∧ (((6 ≤ 10) ∧ ((6 % 2 = 0) ∧ (8 ≥ 1))) ∧ (((8 ≤ 10) ∧ (8 % 2 = 0)) ∧ ((10 ≥ 1) ∧ (10 ≤ 10)))))

def R1 : Prop := ((((10 % 2 = 0) ∧ ((2 ≠ 4) ∧ (2 ≠ 6))) ∧ (((2 ≠ 8) ∧ (2 ≠ 10)) ∧ ((4 ≠ 6) ∧ (4 ≠ 8)))) ∧ (((4 ≠ 10) ∧ ((6 ≠ 8) ∧ (6 ≠ 10))) ∧ (((8 ≠ 10) ∧ (11 % 2 = 1)) ∧ ((2 ≠ 11) ∧ (4 ≠ 11)))))

def R2 : Prop := ((((6 ≠ 11) ∧ ((6 ≠ 11) ∧ (8 ≠ 11))) ∧ (((10 ≠ 11) ∧ (12 ≠ 11)) ∧ ((8 ≠ 11) ∧ (10 ≠ 11)))) ∧ (((12 ≠ 11) ∧ ((14 ≠ 11) ∧ (14 ≠ 11))) ∧ (((16 ≠ 11) ∧ (18 ≠ 11)) ∧ ((20 ≠ 11) ∧ (10 ≠ 11)))))

def R3 : Prop := ((((12 ≠ 11) ∧ ((14 ≠ 11) ∧ (16 ≠ 11))) ∧ (((16 ≠ 11) ∧ (18 ≠ 11)) ∧ ((20 ≠ 11) ∧ (22 ≠ 11)))) ∧ (((18 ≠ 11) ∧ ((20 ≠ 11) ∧ (22 ≠ 11))) ∧ (((24 ≠ 11) ∧ (24 ≠ 11)) ∧ ((26 ≠ 11) ∧ (28 ≠ 11)))))

def R4 : Prop := (30 ≠ 11)

theorem jsp299 (R0 ∧ (R1 ∧ (R2 ∧ (R3 ∧ (R4 ∧ True))))) :=

  by

  have hr0 : R0 := by

    have h_0 : (2 ≥ 1) := by decide
    have h_1 : (2 ≤ 10) := by decide
    have h_2 : (2 % 2 = 0) := by decide
    have h_3 : (4 ≥ 1) := by decide
    have h_4 : (4 ≤ 10) := by decide
    have h_5 : (4 % 2 = 0) := by decide
    have h_6 : (6 ≥ 1) := by decide
    have h_7 : (6 ≤ 10) := by decide
    have h_8 : (6 % 2 = 0) := by decide
    have h_9 : (8 ≥ 1) := by decide
    have h_10 : (8 ≤ 10) := by decide
    have h_11 : (8 % 2 = 0) := by decide
    have h_12 : (10 ≥ 1) := by decide
    have h_13 : (10 ≤ 10) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (10 % 2 = 0) := by decide
    have h_15 : (2 ≠ 4) := by decide
    have h_16 : (2 ≠ 6) := by decide
    have h_17 : (2 ≠ 8) := by decide
    have h_18 : (2 ≠ 10) := by decide
    have h_19 : (4 ≠ 6) := by decide
    have h_20 : (4 ≠ 8) := by decide
    have h_21 : (4 ≠ 10) := by decide
    have h_22 : (6 ≠ 8) := by decide
    have h_23 : (6 ≠ 10) := by decide
    have h_24 : (8 ≠ 10) := by decide
    have h_25 : (11 % 2 = 1) := by decide
    have h_26 : (2 ≠ 11) := by decide
    have h_27 : (4 ≠ 11) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (6 ≠ 11) := by decide
    have h_29 : (6 ≠ 11) := by decide
    have h_30 : (8 ≠ 11) := by decide
    have h_31 : (10 ≠ 11) := by decide
    have h_32 : (12 ≠ 11) := by decide
    have h_33 : (8 ≠ 11) := by decide
    have h_34 : (10 ≠ 11) := by decide
    have h_35 : (12 ≠ 11) := by decide
    have h_36 : (14 ≠ 11) := by decide
    have h_37 : (14 ≠ 11) := by decide
    have h_38 : (16 ≠ 11) := by decide
    have h_39 : (18 ≠ 11) := by decide
    have h_40 : (20 ≠ 11) := by decide
    have h_41 : (10 ≠ 11) := by decide
    exact ⟨⟨⟨h_28, ⟨h_29, h_30⟩⟩, ⟨⟨h_31, h_32⟩, ⟨h_33, h_34⟩⟩⟩, ⟨⟨h_35, ⟨h_36, h_37⟩⟩, ⟨⟨h_38, h_39⟩, ⟨h_40, h_41⟩⟩⟩⟩

  have hr3 : R3 := by

    have h_42 : (12 ≠ 11) := by decide
    have h_43 : (14 ≠ 11) := by decide
    have h_44 : (16 ≠ 11) := by decide
    have h_45 : (16 ≠ 11) := by decide
    have h_46 : (18 ≠ 11) := by decide
    have h_47 : (20 ≠ 11) := by decide
    have h_48 : (22 ≠ 11) := by decide
    have h_49 : (18 ≠ 11) := by decide
    have h_50 : (20 ≠ 11) := by decide
    have h_51 : (22 ≠ 11) := by decide
    have h_52 : (24 ≠ 11) := by decide
    have h_53 : (24 ≠ 11) := by decide
    have h_54 : (26 ≠ 11) := by decide
    have h_55 : (28 ≠ 11) := by decide
    exact ⟨⟨⟨h_42, ⟨h_43, h_44⟩⟩, ⟨⟨h_45, h_46⟩, ⟨h_47, h_48⟩⟩⟩, ⟨⟨h_49, ⟨h_50, h_51⟩⟩, ⟨⟨h_52, h_53⟩, ⟨h_54, h_55⟩⟩⟩⟩

  have hr4 : R4 := by

    have h_56 : (30 ≠ 11) := by decide
    exact h_56

  constructor

  · exact hr0

  · exact hr1

  · exact hr2

  · exact hr3

  · trivial

