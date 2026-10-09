-- =====================================================================
-- JSP-000055 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：practical numbers
--       例证：12 是 practical 数：12 的每个正因子为 1, 2, 3, 4, 6, 12，
--       且每个整数 1 ≤ t ≤ 11 均可表示为这些因子中若干互异者之和：
--       1 = 1、2 = 2、3 = 3、4 = 4、5 = 2+3、6 = 6、7 = 1+6、
--       8 = 2+6、9 = 3+6、10 = 4+6、11 = 1+4+6。
--       全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp55.lean
-- =====================================================================

set_option maxRecDepth 1000000


def R0 : Prop := ((((12 % 1 = 0) ∧ ((12 % 2 = 0) ∧ (12 % 3 = 0))) ∧ (((12 % 4 = 0) ∧ (12 % 6 = 0)) ∧ ((12 % 12 = 0) ∧ (1 ≠ 2)))) ∧ (((1 ≠ 3) ∧ ((1 ≠ 4) ∧ (1 ≠ 6))) ∧ (((1 ≠ 12) ∧ (2 ≠ 3)) ∧ ((2 ≠ 4) ∧ (2 ≠ 6)))))

def R1 : Prop := ((((2 ≠ 12) ∧ ((3 ≠ 4) ∧ (3 ≠ 6))) ∧ (((3 ≠ 12) ∧ (4 ≠ 6)) ∧ ((4 ≠ 12) ∧ (6 ≠ 12)))) ∧ (((1 = 1) ∧ ((2 = 2) ∧ (3 = 3))) ∧ (((4 = 4) ∧ (2 + 3 = 5)) ∧ ((6 = 6) ∧ (1 + 6 = 7)))))

def R2 : Prop := (((2 + 6 = 8) ∧ (3 + 6 = 9)) ∧ ((4 + 6 = 10) ∧ (1 + 4 + 6 = 11)))

theorem jsp55 (R0 ∧ (R1 ∧ (R2 ∧ True))) :=

  by

  have hr0 : R0 := by

    have h_0 : (12 % 1 = 0) := by decide
    have h_1 : (12 % 2 = 0) := by decide
    have h_2 : (12 % 3 = 0) := by decide
    have h_3 : (12 % 4 = 0) := by decide
    have h_4 : (12 % 6 = 0) := by decide
    have h_5 : (12 % 12 = 0) := by decide
    have h_6 : (1 ≠ 2) := by decide
    have h_7 : (1 ≠ 3) := by decide
    have h_8 : (1 ≠ 4) := by decide
    have h_9 : (1 ≠ 6) := by decide
    have h_10 : (1 ≠ 12) := by decide
    have h_11 : (2 ≠ 3) := by decide
    have h_12 : (2 ≠ 4) := by decide
    have h_13 : (2 ≠ 6) := by decide
    exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩

  have hr1 : R1 := by

    have h_14 : (2 ≠ 12) := by decide
    have h_15 : (3 ≠ 4) := by decide
    have h_16 : (3 ≠ 6) := by decide
    have h_17 : (3 ≠ 12) := by decide
    have h_18 : (4 ≠ 6) := by decide
    have h_19 : (4 ≠ 12) := by decide
    have h_20 : (6 ≠ 12) := by decide
    have h_21 : (1 = 1) := by decide
    have h_22 : (2 = 2) := by decide
    have h_23 : (3 = 3) := by decide
    have h_24 : (4 = 4) := by decide
    have h_25 : (2 + 3 = 5) := by decide
    have h_26 : (6 = 6) := by decide
    have h_27 : (1 + 6 = 7) := by decide
    exact ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩

  have hr2 : R2 := by

    have h_28 : (2 + 6 = 8) := by decide
    have h_29 : (3 + 6 = 9) := by decide
    have h_30 : (4 + 6 = 10) := by decide
    have h_31 : (1 + 4 + 6 = 11) := by decide
    exact ⟨⟨h_28, h_29⟩, ⟨h_30, h_31⟩⟩

  constructor

  · exact hr0

  · exact hr1

  · trivial

