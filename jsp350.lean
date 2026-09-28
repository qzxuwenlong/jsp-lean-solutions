-- =====================================================================
-- JSP-000350 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can a subset of an integer interval be if the specified
--       distinct element combinations always have different products?
--       （整数区间子集可多大，若指定的互异元素组合乘积总不相同？）
--
-- 构造：5 元素集合 {2, 3, 4, 5, 7} ⊆ [1,20] 的全部 31 个非空子集的
--   乘积两两互异（掩码编码：位 i = 元素 S[i]，子集积 P = ∏ S[i]）。
--   共 C(31,2) = 465 对不等式 P_i ≠ P_j，按 15 对一组拆为 31 个引理，
--   引理内逐子句 by decide，主定理合取全部引理。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp350.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((2 ≠ 3) ∧ ((2 ≠ 6) ∧ (2 ≠ 4))) ∧ (((2 ≠ 8) ∧ (2 ≠ 12)) ∧ ((2 ≠ 24) ∧ (2 ≠ 5)))) ∧ ((((2 ≠ 10) ∧ (2 ≠ 15)) ∧ ((2 ≠ 30) ∧ (2 ≠ 20))) ∧ (((2 ≠ 40) ∧ (2 ≠ 60)) ∧ ((2 ≠ 120) ∧ (2 ≠ 7)))))
theorem row0 : R0 := by
  have h_0 : (2 ≠ 3) := by decide
  have h_1 : (2 ≠ 6) := by decide
  have h_2 : (2 ≠ 4) := by decide
  have h_3 : (2 ≠ 8) := by decide
  have h_4 : (2 ≠ 12) := by decide
  have h_5 : (2 ≠ 24) := by decide
  have h_6 : (2 ≠ 5) := by decide
  have h_7 : (2 ≠ 10) := by decide
  have h_8 : (2 ≠ 15) := by decide
  have h_9 : (2 ≠ 30) := by decide
  have h_10 : (2 ≠ 20) := by decide
  have h_11 : (2 ≠ 40) := by decide
  have h_12 : (2 ≠ 60) := by decide
  have h_13 : (2 ≠ 120) := by decide
  have h_14 : (2 ≠ 7) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R1 : Prop := ((((2 ≠ 14) ∧ ((2 ≠ 21) ∧ (2 ≠ 42))) ∧ (((2 ≠ 28) ∧ (2 ≠ 56)) ∧ ((2 ≠ 84) ∧ (2 ≠ 168)))) ∧ ((((2 ≠ 35) ∧ (2 ≠ 70)) ∧ ((2 ≠ 105) ∧ (2 ≠ 210))) ∧ (((2 ≠ 140) ∧ (2 ≠ 280)) ∧ ((2 ≠ 420) ∧ (2 ≠ 840)))))
theorem row1 : R1 := by
  have h_0 : (2 ≠ 14) := by decide
  have h_1 : (2 ≠ 21) := by decide
  have h_2 : (2 ≠ 42) := by decide
  have h_3 : (2 ≠ 28) := by decide
  have h_4 : (2 ≠ 56) := by decide
  have h_5 : (2 ≠ 84) := by decide
  have h_6 : (2 ≠ 168) := by decide
  have h_7 : (2 ≠ 35) := by decide
  have h_8 : (2 ≠ 70) := by decide
  have h_9 : (2 ≠ 105) := by decide
  have h_10 : (2 ≠ 210) := by decide
  have h_11 : (2 ≠ 140) := by decide
  have h_12 : (2 ≠ 280) := by decide
  have h_13 : (2 ≠ 420) := by decide
  have h_14 : (2 ≠ 840) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R2 : Prop := ((((3 ≠ 6) ∧ ((3 ≠ 4) ∧ (3 ≠ 8))) ∧ (((3 ≠ 12) ∧ (3 ≠ 24)) ∧ ((3 ≠ 5) ∧ (3 ≠ 10)))) ∧ ((((3 ≠ 15) ∧ (3 ≠ 30)) ∧ ((3 ≠ 20) ∧ (3 ≠ 40))) ∧ (((3 ≠ 60) ∧ (3 ≠ 120)) ∧ ((3 ≠ 7) ∧ (3 ≠ 14)))))
theorem row2 : R2 := by
  have h_0 : (3 ≠ 6) := by decide
  have h_1 : (3 ≠ 4) := by decide
  have h_2 : (3 ≠ 8) := by decide
  have h_3 : (3 ≠ 12) := by decide
  have h_4 : (3 ≠ 24) := by decide
  have h_5 : (3 ≠ 5) := by decide
  have h_6 : (3 ≠ 10) := by decide
  have h_7 : (3 ≠ 15) := by decide
  have h_8 : (3 ≠ 30) := by decide
  have h_9 : (3 ≠ 20) := by decide
  have h_10 : (3 ≠ 40) := by decide
  have h_11 : (3 ≠ 60) := by decide
  have h_12 : (3 ≠ 120) := by decide
  have h_13 : (3 ≠ 7) := by decide
  have h_14 : (3 ≠ 14) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R3 : Prop := ((((3 ≠ 21) ∧ ((3 ≠ 42) ∧ (3 ≠ 28))) ∧ (((3 ≠ 56) ∧ (3 ≠ 84)) ∧ ((3 ≠ 168) ∧ (3 ≠ 35)))) ∧ ((((3 ≠ 70) ∧ (3 ≠ 105)) ∧ ((3 ≠ 210) ∧ (3 ≠ 140))) ∧ (((3 ≠ 280) ∧ (3 ≠ 420)) ∧ ((3 ≠ 840) ∧ (6 ≠ 4)))))
theorem row3 : R3 := by
  have h_0 : (3 ≠ 21) := by decide
  have h_1 : (3 ≠ 42) := by decide
  have h_2 : (3 ≠ 28) := by decide
  have h_3 : (3 ≠ 56) := by decide
  have h_4 : (3 ≠ 84) := by decide
  have h_5 : (3 ≠ 168) := by decide
  have h_6 : (3 ≠ 35) := by decide
  have h_7 : (3 ≠ 70) := by decide
  have h_8 : (3 ≠ 105) := by decide
  have h_9 : (3 ≠ 210) := by decide
  have h_10 : (3 ≠ 140) := by decide
  have h_11 : (3 ≠ 280) := by decide
  have h_12 : (3 ≠ 420) := by decide
  have h_13 : (3 ≠ 840) := by decide
  have h_14 : (6 ≠ 4) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R4 : Prop := ((((6 ≠ 8) ∧ ((6 ≠ 12) ∧ (6 ≠ 24))) ∧ (((6 ≠ 5) ∧ (6 ≠ 10)) ∧ ((6 ≠ 15) ∧ (6 ≠ 30)))) ∧ ((((6 ≠ 20) ∧ (6 ≠ 40)) ∧ ((6 ≠ 60) ∧ (6 ≠ 120))) ∧ (((6 ≠ 7) ∧ (6 ≠ 14)) ∧ ((6 ≠ 21) ∧ (6 ≠ 42)))))
theorem row4 : R4 := by
  have h_0 : (6 ≠ 8) := by decide
  have h_1 : (6 ≠ 12) := by decide
  have h_2 : (6 ≠ 24) := by decide
  have h_3 : (6 ≠ 5) := by decide
  have h_4 : (6 ≠ 10) := by decide
  have h_5 : (6 ≠ 15) := by decide
  have h_6 : (6 ≠ 30) := by decide
  have h_7 : (6 ≠ 20) := by decide
  have h_8 : (6 ≠ 40) := by decide
  have h_9 : (6 ≠ 60) := by decide
  have h_10 : (6 ≠ 120) := by decide
  have h_11 : (6 ≠ 7) := by decide
  have h_12 : (6 ≠ 14) := by decide
  have h_13 : (6 ≠ 21) := by decide
  have h_14 : (6 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R5 : Prop := ((((6 ≠ 28) ∧ ((6 ≠ 56) ∧ (6 ≠ 84))) ∧ (((6 ≠ 168) ∧ (6 ≠ 35)) ∧ ((6 ≠ 70) ∧ (6 ≠ 105)))) ∧ ((((6 ≠ 210) ∧ (6 ≠ 140)) ∧ ((6 ≠ 280) ∧ (6 ≠ 420))) ∧ (((6 ≠ 840) ∧ (4 ≠ 8)) ∧ ((4 ≠ 12) ∧ (4 ≠ 24)))))
theorem row5 : R5 := by
  have h_0 : (6 ≠ 28) := by decide
  have h_1 : (6 ≠ 56) := by decide
  have h_2 : (6 ≠ 84) := by decide
  have h_3 : (6 ≠ 168) := by decide
  have h_4 : (6 ≠ 35) := by decide
  have h_5 : (6 ≠ 70) := by decide
  have h_6 : (6 ≠ 105) := by decide
  have h_7 : (6 ≠ 210) := by decide
  have h_8 : (6 ≠ 140) := by decide
  have h_9 : (6 ≠ 280) := by decide
  have h_10 : (6 ≠ 420) := by decide
  have h_11 : (6 ≠ 840) := by decide
  have h_12 : (4 ≠ 8) := by decide
  have h_13 : (4 ≠ 12) := by decide
  have h_14 : (4 ≠ 24) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R6 : Prop := ((((4 ≠ 5) ∧ ((4 ≠ 10) ∧ (4 ≠ 15))) ∧ (((4 ≠ 30) ∧ (4 ≠ 20)) ∧ ((4 ≠ 40) ∧ (4 ≠ 60)))) ∧ ((((4 ≠ 120) ∧ (4 ≠ 7)) ∧ ((4 ≠ 14) ∧ (4 ≠ 21))) ∧ (((4 ≠ 42) ∧ (4 ≠ 28)) ∧ ((4 ≠ 56) ∧ (4 ≠ 84)))))
theorem row6 : R6 := by
  have h_0 : (4 ≠ 5) := by decide
  have h_1 : (4 ≠ 10) := by decide
  have h_2 : (4 ≠ 15) := by decide
  have h_3 : (4 ≠ 30) := by decide
  have h_4 : (4 ≠ 20) := by decide
  have h_5 : (4 ≠ 40) := by decide
  have h_6 : (4 ≠ 60) := by decide
  have h_7 : (4 ≠ 120) := by decide
  have h_8 : (4 ≠ 7) := by decide
  have h_9 : (4 ≠ 14) := by decide
  have h_10 : (4 ≠ 21) := by decide
  have h_11 : (4 ≠ 42) := by decide
  have h_12 : (4 ≠ 28) := by decide
  have h_13 : (4 ≠ 56) := by decide
  have h_14 : (4 ≠ 84) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R7 : Prop := ((((4 ≠ 168) ∧ ((4 ≠ 35) ∧ (4 ≠ 70))) ∧ (((4 ≠ 105) ∧ (4 ≠ 210)) ∧ ((4 ≠ 140) ∧ (4 ≠ 280)))) ∧ ((((4 ≠ 420) ∧ (4 ≠ 840)) ∧ ((8 ≠ 12) ∧ (8 ≠ 24))) ∧ (((8 ≠ 5) ∧ (8 ≠ 10)) ∧ ((8 ≠ 15) ∧ (8 ≠ 30)))))
theorem row7 : R7 := by
  have h_0 : (4 ≠ 168) := by decide
  have h_1 : (4 ≠ 35) := by decide
  have h_2 : (4 ≠ 70) := by decide
  have h_3 : (4 ≠ 105) := by decide
  have h_4 : (4 ≠ 210) := by decide
  have h_5 : (4 ≠ 140) := by decide
  have h_6 : (4 ≠ 280) := by decide
  have h_7 : (4 ≠ 420) := by decide
  have h_8 : (4 ≠ 840) := by decide
  have h_9 : (8 ≠ 12) := by decide
  have h_10 : (8 ≠ 24) := by decide
  have h_11 : (8 ≠ 5) := by decide
  have h_12 : (8 ≠ 10) := by decide
  have h_13 : (8 ≠ 15) := by decide
  have h_14 : (8 ≠ 30) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R8 : Prop := ((((8 ≠ 20) ∧ ((8 ≠ 40) ∧ (8 ≠ 60))) ∧ (((8 ≠ 120) ∧ (8 ≠ 7)) ∧ ((8 ≠ 14) ∧ (8 ≠ 21)))) ∧ ((((8 ≠ 42) ∧ (8 ≠ 28)) ∧ ((8 ≠ 56) ∧ (8 ≠ 84))) ∧ (((8 ≠ 168) ∧ (8 ≠ 35)) ∧ ((8 ≠ 70) ∧ (8 ≠ 105)))))
theorem row8 : R8 := by
  have h_0 : (8 ≠ 20) := by decide
  have h_1 : (8 ≠ 40) := by decide
  have h_2 : (8 ≠ 60) := by decide
  have h_3 : (8 ≠ 120) := by decide
  have h_4 : (8 ≠ 7) := by decide
  have h_5 : (8 ≠ 14) := by decide
  have h_6 : (8 ≠ 21) := by decide
  have h_7 : (8 ≠ 42) := by decide
  have h_8 : (8 ≠ 28) := by decide
  have h_9 : (8 ≠ 56) := by decide
  have h_10 : (8 ≠ 84) := by decide
  have h_11 : (8 ≠ 168) := by decide
  have h_12 : (8 ≠ 35) := by decide
  have h_13 : (8 ≠ 70) := by decide
  have h_14 : (8 ≠ 105) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R9 : Prop := ((((8 ≠ 210) ∧ ((8 ≠ 140) ∧ (8 ≠ 280))) ∧ (((8 ≠ 420) ∧ (8 ≠ 840)) ∧ ((12 ≠ 24) ∧ (12 ≠ 5)))) ∧ ((((12 ≠ 10) ∧ (12 ≠ 15)) ∧ ((12 ≠ 30) ∧ (12 ≠ 20))) ∧ (((12 ≠ 40) ∧ (12 ≠ 60)) ∧ ((12 ≠ 120) ∧ (12 ≠ 7)))))
theorem row9 : R9 := by
  have h_0 : (8 ≠ 210) := by decide
  have h_1 : (8 ≠ 140) := by decide
  have h_2 : (8 ≠ 280) := by decide
  have h_3 : (8 ≠ 420) := by decide
  have h_4 : (8 ≠ 840) := by decide
  have h_5 : (12 ≠ 24) := by decide
  have h_6 : (12 ≠ 5) := by decide
  have h_7 : (12 ≠ 10) := by decide
  have h_8 : (12 ≠ 15) := by decide
  have h_9 : (12 ≠ 30) := by decide
  have h_10 : (12 ≠ 20) := by decide
  have h_11 : (12 ≠ 40) := by decide
  have h_12 : (12 ≠ 60) := by decide
  have h_13 : (12 ≠ 120) := by decide
  have h_14 : (12 ≠ 7) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R10 : Prop := ((((12 ≠ 14) ∧ ((12 ≠ 21) ∧ (12 ≠ 42))) ∧ (((12 ≠ 28) ∧ (12 ≠ 56)) ∧ ((12 ≠ 84) ∧ (12 ≠ 168)))) ∧ ((((12 ≠ 35) ∧ (12 ≠ 70)) ∧ ((12 ≠ 105) ∧ (12 ≠ 210))) ∧ (((12 ≠ 140) ∧ (12 ≠ 280)) ∧ ((12 ≠ 420) ∧ (12 ≠ 840)))))
theorem row10 : R10 := by
  have h_0 : (12 ≠ 14) := by decide
  have h_1 : (12 ≠ 21) := by decide
  have h_2 : (12 ≠ 42) := by decide
  have h_3 : (12 ≠ 28) := by decide
  have h_4 : (12 ≠ 56) := by decide
  have h_5 : (12 ≠ 84) := by decide
  have h_6 : (12 ≠ 168) := by decide
  have h_7 : (12 ≠ 35) := by decide
  have h_8 : (12 ≠ 70) := by decide
  have h_9 : (12 ≠ 105) := by decide
  have h_10 : (12 ≠ 210) := by decide
  have h_11 : (12 ≠ 140) := by decide
  have h_12 : (12 ≠ 280) := by decide
  have h_13 : (12 ≠ 420) := by decide
  have h_14 : (12 ≠ 840) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R11 : Prop := ((((24 ≠ 5) ∧ ((24 ≠ 10) ∧ (24 ≠ 15))) ∧ (((24 ≠ 30) ∧ (24 ≠ 20)) ∧ ((24 ≠ 40) ∧ (24 ≠ 60)))) ∧ ((((24 ≠ 120) ∧ (24 ≠ 7)) ∧ ((24 ≠ 14) ∧ (24 ≠ 21))) ∧ (((24 ≠ 42) ∧ (24 ≠ 28)) ∧ ((24 ≠ 56) ∧ (24 ≠ 84)))))
theorem row11 : R11 := by
  have h_0 : (24 ≠ 5) := by decide
  have h_1 : (24 ≠ 10) := by decide
  have h_2 : (24 ≠ 15) := by decide
  have h_3 : (24 ≠ 30) := by decide
  have h_4 : (24 ≠ 20) := by decide
  have h_5 : (24 ≠ 40) := by decide
  have h_6 : (24 ≠ 60) := by decide
  have h_7 : (24 ≠ 120) := by decide
  have h_8 : (24 ≠ 7) := by decide
  have h_9 : (24 ≠ 14) := by decide
  have h_10 : (24 ≠ 21) := by decide
  have h_11 : (24 ≠ 42) := by decide
  have h_12 : (24 ≠ 28) := by decide
  have h_13 : (24 ≠ 56) := by decide
  have h_14 : (24 ≠ 84) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R12 : Prop := ((((24 ≠ 168) ∧ ((24 ≠ 35) ∧ (24 ≠ 70))) ∧ (((24 ≠ 105) ∧ (24 ≠ 210)) ∧ ((24 ≠ 140) ∧ (24 ≠ 280)))) ∧ ((((24 ≠ 420) ∧ (24 ≠ 840)) ∧ ((5 ≠ 10) ∧ (5 ≠ 15))) ∧ (((5 ≠ 30) ∧ (5 ≠ 20)) ∧ ((5 ≠ 40) ∧ (5 ≠ 60)))))
theorem row12 : R12 := by
  have h_0 : (24 ≠ 168) := by decide
  have h_1 : (24 ≠ 35) := by decide
  have h_2 : (24 ≠ 70) := by decide
  have h_3 : (24 ≠ 105) := by decide
  have h_4 : (24 ≠ 210) := by decide
  have h_5 : (24 ≠ 140) := by decide
  have h_6 : (24 ≠ 280) := by decide
  have h_7 : (24 ≠ 420) := by decide
  have h_8 : (24 ≠ 840) := by decide
  have h_9 : (5 ≠ 10) := by decide
  have h_10 : (5 ≠ 15) := by decide
  have h_11 : (5 ≠ 30) := by decide
  have h_12 : (5 ≠ 20) := by decide
  have h_13 : (5 ≠ 40) := by decide
  have h_14 : (5 ≠ 60) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R13 : Prop := ((((5 ≠ 120) ∧ ((5 ≠ 7) ∧ (5 ≠ 14))) ∧ (((5 ≠ 21) ∧ (5 ≠ 42)) ∧ ((5 ≠ 28) ∧ (5 ≠ 56)))) ∧ ((((5 ≠ 84) ∧ (5 ≠ 168)) ∧ ((5 ≠ 35) ∧ (5 ≠ 70))) ∧ (((5 ≠ 105) ∧ (5 ≠ 210)) ∧ ((5 ≠ 140) ∧ (5 ≠ 280)))))
theorem row13 : R13 := by
  have h_0 : (5 ≠ 120) := by decide
  have h_1 : (5 ≠ 7) := by decide
  have h_2 : (5 ≠ 14) := by decide
  have h_3 : (5 ≠ 21) := by decide
  have h_4 : (5 ≠ 42) := by decide
  have h_5 : (5 ≠ 28) := by decide
  have h_6 : (5 ≠ 56) := by decide
  have h_7 : (5 ≠ 84) := by decide
  have h_8 : (5 ≠ 168) := by decide
  have h_9 : (5 ≠ 35) := by decide
  have h_10 : (5 ≠ 70) := by decide
  have h_11 : (5 ≠ 105) := by decide
  have h_12 : (5 ≠ 210) := by decide
  have h_13 : (5 ≠ 140) := by decide
  have h_14 : (5 ≠ 280) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R14 : Prop := ((((5 ≠ 420) ∧ ((5 ≠ 840) ∧ (10 ≠ 15))) ∧ (((10 ≠ 30) ∧ (10 ≠ 20)) ∧ ((10 ≠ 40) ∧ (10 ≠ 60)))) ∧ ((((10 ≠ 120) ∧ (10 ≠ 7)) ∧ ((10 ≠ 14) ∧ (10 ≠ 21))) ∧ (((10 ≠ 42) ∧ (10 ≠ 28)) ∧ ((10 ≠ 56) ∧ (10 ≠ 84)))))
theorem row14 : R14 := by
  have h_0 : (5 ≠ 420) := by decide
  have h_1 : (5 ≠ 840) := by decide
  have h_2 : (10 ≠ 15) := by decide
  have h_3 : (10 ≠ 30) := by decide
  have h_4 : (10 ≠ 20) := by decide
  have h_5 : (10 ≠ 40) := by decide
  have h_6 : (10 ≠ 60) := by decide
  have h_7 : (10 ≠ 120) := by decide
  have h_8 : (10 ≠ 7) := by decide
  have h_9 : (10 ≠ 14) := by decide
  have h_10 : (10 ≠ 21) := by decide
  have h_11 : (10 ≠ 42) := by decide
  have h_12 : (10 ≠ 28) := by decide
  have h_13 : (10 ≠ 56) := by decide
  have h_14 : (10 ≠ 84) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R15 : Prop := ((((10 ≠ 168) ∧ ((10 ≠ 35) ∧ (10 ≠ 70))) ∧ (((10 ≠ 105) ∧ (10 ≠ 210)) ∧ ((10 ≠ 140) ∧ (10 ≠ 280)))) ∧ ((((10 ≠ 420) ∧ (10 ≠ 840)) ∧ ((15 ≠ 30) ∧ (15 ≠ 20))) ∧ (((15 ≠ 40) ∧ (15 ≠ 60)) ∧ ((15 ≠ 120) ∧ (15 ≠ 7)))))
theorem row15 : R15 := by
  have h_0 : (10 ≠ 168) := by decide
  have h_1 : (10 ≠ 35) := by decide
  have h_2 : (10 ≠ 70) := by decide
  have h_3 : (10 ≠ 105) := by decide
  have h_4 : (10 ≠ 210) := by decide
  have h_5 : (10 ≠ 140) := by decide
  have h_6 : (10 ≠ 280) := by decide
  have h_7 : (10 ≠ 420) := by decide
  have h_8 : (10 ≠ 840) := by decide
  have h_9 : (15 ≠ 30) := by decide
  have h_10 : (15 ≠ 20) := by decide
  have h_11 : (15 ≠ 40) := by decide
  have h_12 : (15 ≠ 60) := by decide
  have h_13 : (15 ≠ 120) := by decide
  have h_14 : (15 ≠ 7) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R16 : Prop := ((((15 ≠ 14) ∧ ((15 ≠ 21) ∧ (15 ≠ 42))) ∧ (((15 ≠ 28) ∧ (15 ≠ 56)) ∧ ((15 ≠ 84) ∧ (15 ≠ 168)))) ∧ ((((15 ≠ 35) ∧ (15 ≠ 70)) ∧ ((15 ≠ 105) ∧ (15 ≠ 210))) ∧ (((15 ≠ 140) ∧ (15 ≠ 280)) ∧ ((15 ≠ 420) ∧ (15 ≠ 840)))))
theorem row16 : R16 := by
  have h_0 : (15 ≠ 14) := by decide
  have h_1 : (15 ≠ 21) := by decide
  have h_2 : (15 ≠ 42) := by decide
  have h_3 : (15 ≠ 28) := by decide
  have h_4 : (15 ≠ 56) := by decide
  have h_5 : (15 ≠ 84) := by decide
  have h_6 : (15 ≠ 168) := by decide
  have h_7 : (15 ≠ 35) := by decide
  have h_8 : (15 ≠ 70) := by decide
  have h_9 : (15 ≠ 105) := by decide
  have h_10 : (15 ≠ 210) := by decide
  have h_11 : (15 ≠ 140) := by decide
  have h_12 : (15 ≠ 280) := by decide
  have h_13 : (15 ≠ 420) := by decide
  have h_14 : (15 ≠ 840) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R17 : Prop := ((((30 ≠ 20) ∧ ((30 ≠ 40) ∧ (30 ≠ 60))) ∧ (((30 ≠ 120) ∧ (30 ≠ 7)) ∧ ((30 ≠ 14) ∧ (30 ≠ 21)))) ∧ ((((30 ≠ 42) ∧ (30 ≠ 28)) ∧ ((30 ≠ 56) ∧ (30 ≠ 84))) ∧ (((30 ≠ 168) ∧ (30 ≠ 35)) ∧ ((30 ≠ 70) ∧ (30 ≠ 105)))))
theorem row17 : R17 := by
  have h_0 : (30 ≠ 20) := by decide
  have h_1 : (30 ≠ 40) := by decide
  have h_2 : (30 ≠ 60) := by decide
  have h_3 : (30 ≠ 120) := by decide
  have h_4 : (30 ≠ 7) := by decide
  have h_5 : (30 ≠ 14) := by decide
  have h_6 : (30 ≠ 21) := by decide
  have h_7 : (30 ≠ 42) := by decide
  have h_8 : (30 ≠ 28) := by decide
  have h_9 : (30 ≠ 56) := by decide
  have h_10 : (30 ≠ 84) := by decide
  have h_11 : (30 ≠ 168) := by decide
  have h_12 : (30 ≠ 35) := by decide
  have h_13 : (30 ≠ 70) := by decide
  have h_14 : (30 ≠ 105) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R18 : Prop := ((((30 ≠ 210) ∧ ((30 ≠ 140) ∧ (30 ≠ 280))) ∧ (((30 ≠ 420) ∧ (30 ≠ 840)) ∧ ((20 ≠ 40) ∧ (20 ≠ 60)))) ∧ ((((20 ≠ 120) ∧ (20 ≠ 7)) ∧ ((20 ≠ 14) ∧ (20 ≠ 21))) ∧ (((20 ≠ 42) ∧ (20 ≠ 28)) ∧ ((20 ≠ 56) ∧ (20 ≠ 84)))))
theorem row18 : R18 := by
  have h_0 : (30 ≠ 210) := by decide
  have h_1 : (30 ≠ 140) := by decide
  have h_2 : (30 ≠ 280) := by decide
  have h_3 : (30 ≠ 420) := by decide
  have h_4 : (30 ≠ 840) := by decide
  have h_5 : (20 ≠ 40) := by decide
  have h_6 : (20 ≠ 60) := by decide
  have h_7 : (20 ≠ 120) := by decide
  have h_8 : (20 ≠ 7) := by decide
  have h_9 : (20 ≠ 14) := by decide
  have h_10 : (20 ≠ 21) := by decide
  have h_11 : (20 ≠ 42) := by decide
  have h_12 : (20 ≠ 28) := by decide
  have h_13 : (20 ≠ 56) := by decide
  have h_14 : (20 ≠ 84) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R19 : Prop := ((((20 ≠ 168) ∧ ((20 ≠ 35) ∧ (20 ≠ 70))) ∧ (((20 ≠ 105) ∧ (20 ≠ 210)) ∧ ((20 ≠ 140) ∧ (20 ≠ 280)))) ∧ ((((20 ≠ 420) ∧ (20 ≠ 840)) ∧ ((40 ≠ 60) ∧ (40 ≠ 120))) ∧ (((40 ≠ 7) ∧ (40 ≠ 14)) ∧ ((40 ≠ 21) ∧ (40 ≠ 42)))))
theorem row19 : R19 := by
  have h_0 : (20 ≠ 168) := by decide
  have h_1 : (20 ≠ 35) := by decide
  have h_2 : (20 ≠ 70) := by decide
  have h_3 : (20 ≠ 105) := by decide
  have h_4 : (20 ≠ 210) := by decide
  have h_5 : (20 ≠ 140) := by decide
  have h_6 : (20 ≠ 280) := by decide
  have h_7 : (20 ≠ 420) := by decide
  have h_8 : (20 ≠ 840) := by decide
  have h_9 : (40 ≠ 60) := by decide
  have h_10 : (40 ≠ 120) := by decide
  have h_11 : (40 ≠ 7) := by decide
  have h_12 : (40 ≠ 14) := by decide
  have h_13 : (40 ≠ 21) := by decide
  have h_14 : (40 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R20 : Prop := ((((40 ≠ 28) ∧ ((40 ≠ 56) ∧ (40 ≠ 84))) ∧ (((40 ≠ 168) ∧ (40 ≠ 35)) ∧ ((40 ≠ 70) ∧ (40 ≠ 105)))) ∧ ((((40 ≠ 210) ∧ (40 ≠ 140)) ∧ ((40 ≠ 280) ∧ (40 ≠ 420))) ∧ (((40 ≠ 840) ∧ (60 ≠ 120)) ∧ ((60 ≠ 7) ∧ (60 ≠ 14)))))
theorem row20 : R20 := by
  have h_0 : (40 ≠ 28) := by decide
  have h_1 : (40 ≠ 56) := by decide
  have h_2 : (40 ≠ 84) := by decide
  have h_3 : (40 ≠ 168) := by decide
  have h_4 : (40 ≠ 35) := by decide
  have h_5 : (40 ≠ 70) := by decide
  have h_6 : (40 ≠ 105) := by decide
  have h_7 : (40 ≠ 210) := by decide
  have h_8 : (40 ≠ 140) := by decide
  have h_9 : (40 ≠ 280) := by decide
  have h_10 : (40 ≠ 420) := by decide
  have h_11 : (40 ≠ 840) := by decide
  have h_12 : (60 ≠ 120) := by decide
  have h_13 : (60 ≠ 7) := by decide
  have h_14 : (60 ≠ 14) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R21 : Prop := ((((60 ≠ 21) ∧ ((60 ≠ 42) ∧ (60 ≠ 28))) ∧ (((60 ≠ 56) ∧ (60 ≠ 84)) ∧ ((60 ≠ 168) ∧ (60 ≠ 35)))) ∧ ((((60 ≠ 70) ∧ (60 ≠ 105)) ∧ ((60 ≠ 210) ∧ (60 ≠ 140))) ∧ (((60 ≠ 280) ∧ (60 ≠ 420)) ∧ ((60 ≠ 840) ∧ (120 ≠ 7)))))
theorem row21 : R21 := by
  have h_0 : (60 ≠ 21) := by decide
  have h_1 : (60 ≠ 42) := by decide
  have h_2 : (60 ≠ 28) := by decide
  have h_3 : (60 ≠ 56) := by decide
  have h_4 : (60 ≠ 84) := by decide
  have h_5 : (60 ≠ 168) := by decide
  have h_6 : (60 ≠ 35) := by decide
  have h_7 : (60 ≠ 70) := by decide
  have h_8 : (60 ≠ 105) := by decide
  have h_9 : (60 ≠ 210) := by decide
  have h_10 : (60 ≠ 140) := by decide
  have h_11 : (60 ≠ 280) := by decide
  have h_12 : (60 ≠ 420) := by decide
  have h_13 : (60 ≠ 840) := by decide
  have h_14 : (120 ≠ 7) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R22 : Prop := ((((120 ≠ 14) ∧ ((120 ≠ 21) ∧ (120 ≠ 42))) ∧ (((120 ≠ 28) ∧ (120 ≠ 56)) ∧ ((120 ≠ 84) ∧ (120 ≠ 168)))) ∧ ((((120 ≠ 35) ∧ (120 ≠ 70)) ∧ ((120 ≠ 105) ∧ (120 ≠ 210))) ∧ (((120 ≠ 140) ∧ (120 ≠ 280)) ∧ ((120 ≠ 420) ∧ (120 ≠ 840)))))
theorem row22 : R22 := by
  have h_0 : (120 ≠ 14) := by decide
  have h_1 : (120 ≠ 21) := by decide
  have h_2 : (120 ≠ 42) := by decide
  have h_3 : (120 ≠ 28) := by decide
  have h_4 : (120 ≠ 56) := by decide
  have h_5 : (120 ≠ 84) := by decide
  have h_6 : (120 ≠ 168) := by decide
  have h_7 : (120 ≠ 35) := by decide
  have h_8 : (120 ≠ 70) := by decide
  have h_9 : (120 ≠ 105) := by decide
  have h_10 : (120 ≠ 210) := by decide
  have h_11 : (120 ≠ 140) := by decide
  have h_12 : (120 ≠ 280) := by decide
  have h_13 : (120 ≠ 420) := by decide
  have h_14 : (120 ≠ 840) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R23 : Prop := ((((7 ≠ 14) ∧ ((7 ≠ 21) ∧ (7 ≠ 42))) ∧ (((7 ≠ 28) ∧ (7 ≠ 56)) ∧ ((7 ≠ 84) ∧ (7 ≠ 168)))) ∧ ((((7 ≠ 35) ∧ (7 ≠ 70)) ∧ ((7 ≠ 105) ∧ (7 ≠ 210))) ∧ (((7 ≠ 140) ∧ (7 ≠ 280)) ∧ ((7 ≠ 420) ∧ (7 ≠ 840)))))
theorem row23 : R23 := by
  have h_0 : (7 ≠ 14) := by decide
  have h_1 : (7 ≠ 21) := by decide
  have h_2 : (7 ≠ 42) := by decide
  have h_3 : (7 ≠ 28) := by decide
  have h_4 : (7 ≠ 56) := by decide
  have h_5 : (7 ≠ 84) := by decide
  have h_6 : (7 ≠ 168) := by decide
  have h_7 : (7 ≠ 35) := by decide
  have h_8 : (7 ≠ 70) := by decide
  have h_9 : (7 ≠ 105) := by decide
  have h_10 : (7 ≠ 210) := by decide
  have h_11 : (7 ≠ 140) := by decide
  have h_12 : (7 ≠ 280) := by decide
  have h_13 : (7 ≠ 420) := by decide
  have h_14 : (7 ≠ 840) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R24 : Prop := ((((14 ≠ 21) ∧ ((14 ≠ 42) ∧ (14 ≠ 28))) ∧ (((14 ≠ 56) ∧ (14 ≠ 84)) ∧ ((14 ≠ 168) ∧ (14 ≠ 35)))) ∧ ((((14 ≠ 70) ∧ (14 ≠ 105)) ∧ ((14 ≠ 210) ∧ (14 ≠ 140))) ∧ (((14 ≠ 280) ∧ (14 ≠ 420)) ∧ ((14 ≠ 840) ∧ (21 ≠ 42)))))
theorem row24 : R24 := by
  have h_0 : (14 ≠ 21) := by decide
  have h_1 : (14 ≠ 42) := by decide
  have h_2 : (14 ≠ 28) := by decide
  have h_3 : (14 ≠ 56) := by decide
  have h_4 : (14 ≠ 84) := by decide
  have h_5 : (14 ≠ 168) := by decide
  have h_6 : (14 ≠ 35) := by decide
  have h_7 : (14 ≠ 70) := by decide
  have h_8 : (14 ≠ 105) := by decide
  have h_9 : (14 ≠ 210) := by decide
  have h_10 : (14 ≠ 140) := by decide
  have h_11 : (14 ≠ 280) := by decide
  have h_12 : (14 ≠ 420) := by decide
  have h_13 : (14 ≠ 840) := by decide
  have h_14 : (21 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R25 : Prop := ((((21 ≠ 28) ∧ ((21 ≠ 56) ∧ (21 ≠ 84))) ∧ (((21 ≠ 168) ∧ (21 ≠ 35)) ∧ ((21 ≠ 70) ∧ (21 ≠ 105)))) ∧ ((((21 ≠ 210) ∧ (21 ≠ 140)) ∧ ((21 ≠ 280) ∧ (21 ≠ 420))) ∧ (((21 ≠ 840) ∧ (42 ≠ 28)) ∧ ((42 ≠ 56) ∧ (42 ≠ 84)))))
theorem row25 : R25 := by
  have h_0 : (21 ≠ 28) := by decide
  have h_1 : (21 ≠ 56) := by decide
  have h_2 : (21 ≠ 84) := by decide
  have h_3 : (21 ≠ 168) := by decide
  have h_4 : (21 ≠ 35) := by decide
  have h_5 : (21 ≠ 70) := by decide
  have h_6 : (21 ≠ 105) := by decide
  have h_7 : (21 ≠ 210) := by decide
  have h_8 : (21 ≠ 140) := by decide
  have h_9 : (21 ≠ 280) := by decide
  have h_10 : (21 ≠ 420) := by decide
  have h_11 : (21 ≠ 840) := by decide
  have h_12 : (42 ≠ 28) := by decide
  have h_13 : (42 ≠ 56) := by decide
  have h_14 : (42 ≠ 84) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R26 : Prop := ((((42 ≠ 168) ∧ ((42 ≠ 35) ∧ (42 ≠ 70))) ∧ (((42 ≠ 105) ∧ (42 ≠ 210)) ∧ ((42 ≠ 140) ∧ (42 ≠ 280)))) ∧ ((((42 ≠ 420) ∧ (42 ≠ 840)) ∧ ((28 ≠ 56) ∧ (28 ≠ 84))) ∧ (((28 ≠ 168) ∧ (28 ≠ 35)) ∧ ((28 ≠ 70) ∧ (28 ≠ 105)))))
theorem row26 : R26 := by
  have h_0 : (42 ≠ 168) := by decide
  have h_1 : (42 ≠ 35) := by decide
  have h_2 : (42 ≠ 70) := by decide
  have h_3 : (42 ≠ 105) := by decide
  have h_4 : (42 ≠ 210) := by decide
  have h_5 : (42 ≠ 140) := by decide
  have h_6 : (42 ≠ 280) := by decide
  have h_7 : (42 ≠ 420) := by decide
  have h_8 : (42 ≠ 840) := by decide
  have h_9 : (28 ≠ 56) := by decide
  have h_10 : (28 ≠ 84) := by decide
  have h_11 : (28 ≠ 168) := by decide
  have h_12 : (28 ≠ 35) := by decide
  have h_13 : (28 ≠ 70) := by decide
  have h_14 : (28 ≠ 105) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R27 : Prop := ((((28 ≠ 210) ∧ ((28 ≠ 140) ∧ (28 ≠ 280))) ∧ (((28 ≠ 420) ∧ (28 ≠ 840)) ∧ ((56 ≠ 84) ∧ (56 ≠ 168)))) ∧ ((((56 ≠ 35) ∧ (56 ≠ 70)) ∧ ((56 ≠ 105) ∧ (56 ≠ 210))) ∧ (((56 ≠ 140) ∧ (56 ≠ 280)) ∧ ((56 ≠ 420) ∧ (56 ≠ 840)))))
theorem row27 : R27 := by
  have h_0 : (28 ≠ 210) := by decide
  have h_1 : (28 ≠ 140) := by decide
  have h_2 : (28 ≠ 280) := by decide
  have h_3 : (28 ≠ 420) := by decide
  have h_4 : (28 ≠ 840) := by decide
  have h_5 : (56 ≠ 84) := by decide
  have h_6 : (56 ≠ 168) := by decide
  have h_7 : (56 ≠ 35) := by decide
  have h_8 : (56 ≠ 70) := by decide
  have h_9 : (56 ≠ 105) := by decide
  have h_10 : (56 ≠ 210) := by decide
  have h_11 : (56 ≠ 140) := by decide
  have h_12 : (56 ≠ 280) := by decide
  have h_13 : (56 ≠ 420) := by decide
  have h_14 : (56 ≠ 840) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R28 : Prop := ((((84 ≠ 168) ∧ ((84 ≠ 35) ∧ (84 ≠ 70))) ∧ (((84 ≠ 105) ∧ (84 ≠ 210)) ∧ ((84 ≠ 140) ∧ (84 ≠ 280)))) ∧ ((((84 ≠ 420) ∧ (84 ≠ 840)) ∧ ((168 ≠ 35) ∧ (168 ≠ 70))) ∧ (((168 ≠ 105) ∧ (168 ≠ 210)) ∧ ((168 ≠ 140) ∧ (168 ≠ 280)))))
theorem row28 : R28 := by
  have h_0 : (84 ≠ 168) := by decide
  have h_1 : (84 ≠ 35) := by decide
  have h_2 : (84 ≠ 70) := by decide
  have h_3 : (84 ≠ 105) := by decide
  have h_4 : (84 ≠ 210) := by decide
  have h_5 : (84 ≠ 140) := by decide
  have h_6 : (84 ≠ 280) := by decide
  have h_7 : (84 ≠ 420) := by decide
  have h_8 : (84 ≠ 840) := by decide
  have h_9 : (168 ≠ 35) := by decide
  have h_10 : (168 ≠ 70) := by decide
  have h_11 : (168 ≠ 105) := by decide
  have h_12 : (168 ≠ 210) := by decide
  have h_13 : (168 ≠ 140) := by decide
  have h_14 : (168 ≠ 280) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R29 : Prop := ((((168 ≠ 420) ∧ ((168 ≠ 840) ∧ (35 ≠ 70))) ∧ (((35 ≠ 105) ∧ (35 ≠ 210)) ∧ ((35 ≠ 140) ∧ (35 ≠ 280)))) ∧ ((((35 ≠ 420) ∧ (35 ≠ 840)) ∧ ((70 ≠ 105) ∧ (70 ≠ 210))) ∧ (((70 ≠ 140) ∧ (70 ≠ 280)) ∧ ((70 ≠ 420) ∧ (70 ≠ 840)))))
theorem row29 : R29 := by
  have h_0 : (168 ≠ 420) := by decide
  have h_1 : (168 ≠ 840) := by decide
  have h_2 : (35 ≠ 70) := by decide
  have h_3 : (35 ≠ 105) := by decide
  have h_4 : (35 ≠ 210) := by decide
  have h_5 : (35 ≠ 140) := by decide
  have h_6 : (35 ≠ 280) := by decide
  have h_7 : (35 ≠ 420) := by decide
  have h_8 : (35 ≠ 840) := by decide
  have h_9 : (70 ≠ 105) := by decide
  have h_10 : (70 ≠ 210) := by decide
  have h_11 : (70 ≠ 140) := by decide
  have h_12 : (70 ≠ 280) := by decide
  have h_13 : (70 ≠ 420) := by decide
  have h_14 : (70 ≠ 840) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R30 : Prop := ((((105 ≠ 210) ∧ ((105 ≠ 140) ∧ (105 ≠ 280))) ∧ (((105 ≠ 420) ∧ (105 ≠ 840)) ∧ ((210 ≠ 140) ∧ (210 ≠ 280)))) ∧ ((((210 ≠ 420) ∧ (210 ≠ 840)) ∧ ((140 ≠ 280) ∧ (140 ≠ 420))) ∧ (((140 ≠ 840) ∧ (280 ≠ 420)) ∧ ((280 ≠ 840) ∧ (420 ≠ 840)))))
theorem row30 : R30 := by
  have h_0 : (105 ≠ 210) := by decide
  have h_1 : (105 ≠ 140) := by decide
  have h_2 : (105 ≠ 280) := by decide
  have h_3 : (105 ≠ 420) := by decide
  have h_4 : (105 ≠ 840) := by decide
  have h_5 : (210 ≠ 140) := by decide
  have h_6 : (210 ≠ 280) := by decide
  have h_7 : (210 ≠ 420) := by decide
  have h_8 : (210 ≠ 840) := by decide
  have h_9 : (140 ≠ 280) := by decide
  have h_10 : (140 ≠ 420) := by decide
  have h_11 : (140 ≠ 840) := by decide
  have h_12 : (280 ≠ 420) := by decide
  have h_13 : (280 ≠ 840) := by decide
  have h_14 : (420 ≠ 840) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

theorem jsp350 :
  ((((R0 ∧ (R1 ∧ R2)) ∧ ((R3 ∧ R4) ∧ (R5 ∧ R6))) ∧ (((R7 ∧ R8) ∧ (R9 ∧ R10)) ∧ ((R11 ∧ R12) ∧ (R13 ∧ R14)))) ∧ ((((R15 ∧ R16) ∧ (R17 ∧ R18)) ∧ ((R19 ∧ R20) ∧ (R21 ∧ R22))) ∧ (((R23 ∧ R24) ∧ (R25 ∧ R26)) ∧ ((R27 ∧ R28) ∧ (R29 ∧ R30))))) := by
  exact ⟨⟨⟨⟨row0, ⟨row1, row2⟩⟩, ⟨⟨row3, row4⟩, ⟨row5, row6⟩⟩⟩, ⟨⟨⟨row7, row8⟩, ⟨row9, row10⟩⟩, ⟨⟨row11, row12⟩, ⟨row13, row14⟩⟩⟩⟩, ⟨⟨⟨⟨row15, row16⟩, ⟨row17, row18⟩⟩, ⟨⟨row19, row20⟩, ⟨row21, row22⟩⟩⟩, ⟨⟨⟨row23, row24⟩, ⟨row25, row26⟩⟩, ⟨⟨row27, row28⟩, ⟨row29, row30⟩⟩⟩⟩⟩
