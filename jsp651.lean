-- =====================================================================
-- JSP-000651 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large a sum-free subset must every finite integer set
--       contain?
--       （每个有限整数集必含多大的 sum-free 子集？）
--
-- 例证：S = {6, 7, 8, 9, 10} 是区间 [1, 10] 的 5 元素 sum-free 子集：
-- 对任意 x, y ∈ S（允许 x = y），有 x + y ≥ 6 + 6 = 12 > 10，
-- 故 x + y 不在 [1, 10] 中，更不在 S 中；即不存在 x + y = z 的
-- 三元组（x, y, z ∈ S）。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp651.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((6 ≥ 1) ∧ ((6 ≤ 10) ∧ (7 ≥ 1))) ∧ (((7 ≤ 10) ∧ (8 ≥ 1)) ∧ ((8 ≤ 10) ∧ (9 ≥ 1)))) ∧ (((9 ≤ 10) ∧ ((10 ≥ 1) ∧ (10 ≤ 10))) ∧ (((6 + 6 > 10) ∧ (6 + 7 > 10)) ∧ ((6 + 8 > 10) ∧ (6 + 9 > 10)))))

def R1 : Prop := ((((6 + 10 > 10) ∧ ((7 + 6 > 10) ∧ (7 + 7 > 10))) ∧ (((7 + 8 > 10) ∧ (7 + 9 > 10)) ∧ ((7 + 10 > 10) ∧ (8 + 6 > 10)))) ∧ (((8 + 7 > 10) ∧ ((8 + 8 > 10) ∧ (8 + 9 > 10))) ∧ (((8 + 10 > 10) ∧ (9 + 6 > 10)) ∧ ((9 + 7 > 10) ∧ (9 + 8 > 10)))))

def R2 : Prop := (((9 + 9 > 10) ∧ ((9 + 10 > 10) ∧ (10 + 6 > 10))) ∧ (((10 + 7 > 10) ∧ (10 + 8 > 10)) ∧ ((10 + 9 > 10) ∧ (10 + 10 > 10))))

theorem jsp651 (R0 ∧ (R1 ∧ (R2 ∧ True))) :=

  by

  have hr0 : R0 := by

    have h_0 : (6 ≥ 1) := by decide
    have h_1 : (6 ≤ 10) := by decide
    have h_2 : (7 ≥ 1) := by decide
    have h_3 : (7 ≤ 10) := by decide
    have h_4 : (8 ≥ 1) := by decide
    have h_5 : (8 ≤ 10) := by decide
    have h_6 : (9 ≥ 1) := by decide
    have h_7 : (9 ≤ 10) := by decide
    have h_8 : (10 ≥ 1) := by decide
    have h_9 : (10 ≤ 10) := by decide
    have h_10 : (6 + 6 > 10) := by decide
    have h_11 : (6 + 7 > 10) := by decide
    have h_12 : (6 + 8 > 10) := by decide
    have h_13 : (6 + 9 > 10) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (6 + 10 > 10) := by decide
    have h_15 : (7 + 6 > 10) := by decide
    have h_16 : (7 + 7 > 10) := by decide
    have h_17 : (7 + 8 > 10) := by decide
    have h_18 : (7 + 9 > 10) := by decide
    have h_19 : (7 + 10 > 10) := by decide
    have h_20 : (8 + 6 > 10) := by decide
    have h_21 : (8 + 7 > 10) := by decide
    have h_22 : (8 + 8 > 10) := by decide
    have h_23 : (8 + 9 > 10) := by decide
    have h_24 : (8 + 10 > 10) := by decide
    have h_25 : (9 + 6 > 10) := by decide
    have h_26 : (9 + 7 > 10) := by decide
    have h_27 : (9 + 8 > 10) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (9 + 9 > 10) := by decide
    have h_29 : (9 + 10 > 10) := by decide
    have h_30 : (10 + 6 > 10) := by decide
    have h_31 : (10 + 7 > 10) := by decide
    have h_32 : (10 + 8 > 10) := by decide
    have h_33 : (10 + 9 > 10) := by decide
    have h_34 : (10 + 10 > 10) := by decide
    exact ⟨⟨h_28, ⟨h_29, h_30⟩⟩, ⟨⟨h_31, h_32⟩, ⟨h_33, h_34⟩⟩⟩

  constructor

  · exact hr0

  · exact hr1

  · trivial

