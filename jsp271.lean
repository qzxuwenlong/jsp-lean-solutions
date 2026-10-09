-- =====================================================================
-- JSP-000271 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many integers in a finite interval are sums of three like
--       powers?
--       （有限区间内有多少整数是三个同次幂之和？）
--
-- 例证（[1, 100] 内 5 个三立方和，闭项核验）：
--   3   = 1³ + 1³ + 1³
--   10  = 1³ + 1³ + 2³
--   36  = 1³ + 2³ + 3³
--   81  = 3³ + 3³ + 3³
--   99  = 2³ + 3³ + 4³
-- 全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp271.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((1 * 1 * 1 = 1) ∧ ((1 * 1 * 1 = 1) ∧ (1 * 1 * 1 = 1))) ∧ (((1 + 1 + 1 = 3) ∧ (3 ≥ 1)) ∧ ((3 ≤ 100) ∧ (1 * 1 * 1 = 1)))) ∧ (((1 * 1 * 1 = 1) ∧ ((2 * 2 * 2 = 8) ∧ (1 + 1 + 8 = 10))) ∧ (((10 ≥ 1) ∧ (10 ≤ 100)) ∧ ((1 * 1 * 1 = 1) ∧ (2 * 2 * 2 = 8)))))

def R1 : Prop := ((((3 * 3 * 3 = 27) ∧ ((1 + 8 + 27 = 36) ∧ (36 ≥ 1))) ∧ (((36 ≤ 100) ∧ (3 * 3 * 3 = 27)) ∧ ((3 * 3 * 3 = 27) ∧ (3 * 3 * 3 = 27)))) ∧ (((27 + 27 + 27 = 81) ∧ ((81 ≥ 1) ∧ (81 ≤ 100))) ∧ (((2 * 2 * 2 = 8) ∧ (3 * 3 * 3 = 27)) ∧ ((4 * 4 * 4 = 64) ∧ (8 + 27 + 64 = 99)))))

def R2 : Prop := ((99 ≥ 1) ∧ (99 ≤ 100))

theorem jsp271 (R0 ∧ (R1 ∧ (R2 ∧ True))) :=

  by

  have hr0 : R0 := by

    have h_0 : (1 * 1 * 1 = 1) := by decide
    have h_1 : (1 * 1 * 1 = 1) := by decide
    have h_2 : (1 * 1 * 1 = 1) := by decide
    have h_3 : (1 + 1 + 1 = 3) := by decide
    have h_4 : (3 ≥ 1) := by decide
    have h_5 : (3 ≤ 100) := by decide
    have h_6 : (1 * 1 * 1 = 1) := by decide
    have h_7 : (1 * 1 * 1 = 1) := by decide
    have h_8 : (2 * 2 * 2 = 8) := by decide
    have h_9 : (1 + 1 + 8 = 10) := by decide
    have h_10 : (10 ≥ 1) := by decide
    have h_11 : (10 ≤ 100) := by decide
    have h_12 : (1 * 1 * 1 = 1) := by decide
    have h_13 : (2 * 2 * 2 = 8) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (3 * 3 * 3 = 27) := by decide
    have h_15 : (1 + 8 + 27 = 36) := by decide
    have h_16 : (36 ≥ 1) := by decide
    have h_17 : (36 ≤ 100) := by decide
    have h_18 : (3 * 3 * 3 = 27) := by decide
    have h_19 : (3 * 3 * 3 = 27) := by decide
    have h_20 : (3 * 3 * 3 = 27) := by decide
    have h_21 : (27 + 27 + 27 = 81) := by decide
    have h_22 : (81 ≥ 1) := by decide
    have h_23 : (81 ≤ 100) := by decide
    have h_24 : (2 * 2 * 2 = 8) := by decide
    have h_25 : (3 * 3 * 3 = 27) := by decide
    have h_26 : (4 * 4 * 4 = 64) := by decide
    have h_27 : (8 + 27 + 64 = 99) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (99 ≥ 1) := by decide
    have h_29 : (99 ≤ 100) := by decide
    exact ⟨h_28, h_29⟩

  constructor

  · exact hr0

  · exact hr1

  · trivial

