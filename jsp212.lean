-- =====================================================================
-- JSP-000212 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can a subset of an integer interval be if all distinct
--       three-element subsets have different sums?
--       （整数区间子集可多大，若所有互异三元素子集的和互不相同？）
--
-- 构造：7 元素集合 {1, 2, 3, 5, 8, 14, 25} ⊆ [1,30] 的全部 C(7,3) = 35
--   个三元素子集的和两两互异（和值 6..47 各出现一次）。
--   共 C(35,2) = 595 对不等式 S_i ≠ S_j，按 15 对一组拆为 40 个引理，
--   引理内逐子句 by decide，主定理合取全部引理。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp212.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((6 ≠ 8) ∧ ((6 ≠ 11) ∧ (6 ≠ 17))) ∧ (((6 ≠ 28) ∧ (6 ≠ 9)) ∧ ((6 ≠ 12) ∧ (6 ≠ 18)))) ∧ ((((6 ≠ 29) ∧ (6 ≠ 14)) ∧ ((6 ≠ 20) ∧ (6 ≠ 31))) ∧ (((6 ≠ 23) ∧ (6 ≠ 34)) ∧ ((6 ≠ 40) ∧ (6 ≠ 10)))))
theorem row0 : R0 := by
  have h_0 : (6 ≠ 8) := by decide
  have h_1 : (6 ≠ 11) := by decide
  have h_2 : (6 ≠ 17) := by decide
  have h_3 : (6 ≠ 28) := by decide
  have h_4 : (6 ≠ 9) := by decide
  have h_5 : (6 ≠ 12) := by decide
  have h_6 : (6 ≠ 18) := by decide
  have h_7 : (6 ≠ 29) := by decide
  have h_8 : (6 ≠ 14) := by decide
  have h_9 : (6 ≠ 20) := by decide
  have h_10 : (6 ≠ 31) := by decide
  have h_11 : (6 ≠ 23) := by decide
  have h_12 : (6 ≠ 34) := by decide
  have h_13 : (6 ≠ 40) := by decide
  have h_14 : (6 ≠ 10) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R1 : Prop := ((((6 ≠ 13) ∧ ((6 ≠ 19) ∧ (6 ≠ 30))) ∧ (((6 ≠ 15) ∧ (6 ≠ 21)) ∧ ((6 ≠ 32) ∧ (6 ≠ 24)))) ∧ ((((6 ≠ 35) ∧ (6 ≠ 41)) ∧ ((6 ≠ 16) ∧ (6 ≠ 22))) ∧ (((6 ≠ 33) ∧ (6 ≠ 25)) ∧ ((6 ≠ 36) ∧ (6 ≠ 42)))))
theorem row1 : R1 := by
  have h_0 : (6 ≠ 13) := by decide
  have h_1 : (6 ≠ 19) := by decide
  have h_2 : (6 ≠ 30) := by decide
  have h_3 : (6 ≠ 15) := by decide
  have h_4 : (6 ≠ 21) := by decide
  have h_5 : (6 ≠ 32) := by decide
  have h_6 : (6 ≠ 24) := by decide
  have h_7 : (6 ≠ 35) := by decide
  have h_8 : (6 ≠ 41) := by decide
  have h_9 : (6 ≠ 16) := by decide
  have h_10 : (6 ≠ 22) := by decide
  have h_11 : (6 ≠ 33) := by decide
  have h_12 : (6 ≠ 25) := by decide
  have h_13 : (6 ≠ 36) := by decide
  have h_14 : (6 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R2 : Prop := ((((6 ≠ 27) ∧ ((6 ≠ 38) ∧ (6 ≠ 44))) ∧ (((6 ≠ 47) ∧ (8 ≠ 11)) ∧ ((8 ≠ 17) ∧ (8 ≠ 28)))) ∧ ((((8 ≠ 9) ∧ (8 ≠ 12)) ∧ ((8 ≠ 18) ∧ (8 ≠ 29))) ∧ (((8 ≠ 14) ∧ (8 ≠ 20)) ∧ ((8 ≠ 31) ∧ (8 ≠ 23)))))
theorem row2 : R2 := by
  have h_0 : (6 ≠ 27) := by decide
  have h_1 : (6 ≠ 38) := by decide
  have h_2 : (6 ≠ 44) := by decide
  have h_3 : (6 ≠ 47) := by decide
  have h_4 : (8 ≠ 11) := by decide
  have h_5 : (8 ≠ 17) := by decide
  have h_6 : (8 ≠ 28) := by decide
  have h_7 : (8 ≠ 9) := by decide
  have h_8 : (8 ≠ 12) := by decide
  have h_9 : (8 ≠ 18) := by decide
  have h_10 : (8 ≠ 29) := by decide
  have h_11 : (8 ≠ 14) := by decide
  have h_12 : (8 ≠ 20) := by decide
  have h_13 : (8 ≠ 31) := by decide
  have h_14 : (8 ≠ 23) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R3 : Prop := ((((8 ≠ 34) ∧ ((8 ≠ 40) ∧ (8 ≠ 10))) ∧ (((8 ≠ 13) ∧ (8 ≠ 19)) ∧ ((8 ≠ 30) ∧ (8 ≠ 15)))) ∧ ((((8 ≠ 21) ∧ (8 ≠ 32)) ∧ ((8 ≠ 24) ∧ (8 ≠ 35))) ∧ (((8 ≠ 41) ∧ (8 ≠ 16)) ∧ ((8 ≠ 22) ∧ (8 ≠ 33)))))
theorem row3 : R3 := by
  have h_0 : (8 ≠ 34) := by decide
  have h_1 : (8 ≠ 40) := by decide
  have h_2 : (8 ≠ 10) := by decide
  have h_3 : (8 ≠ 13) := by decide
  have h_4 : (8 ≠ 19) := by decide
  have h_5 : (8 ≠ 30) := by decide
  have h_6 : (8 ≠ 15) := by decide
  have h_7 : (8 ≠ 21) := by decide
  have h_8 : (8 ≠ 32) := by decide
  have h_9 : (8 ≠ 24) := by decide
  have h_10 : (8 ≠ 35) := by decide
  have h_11 : (8 ≠ 41) := by decide
  have h_12 : (8 ≠ 16) := by decide
  have h_13 : (8 ≠ 22) := by decide
  have h_14 : (8 ≠ 33) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R4 : Prop := ((((8 ≠ 25) ∧ ((8 ≠ 36) ∧ (8 ≠ 42))) ∧ (((8 ≠ 27) ∧ (8 ≠ 38)) ∧ ((8 ≠ 44) ∧ (8 ≠ 47)))) ∧ ((((11 ≠ 17) ∧ (11 ≠ 28)) ∧ ((11 ≠ 9) ∧ (11 ≠ 12))) ∧ (((11 ≠ 18) ∧ (11 ≠ 29)) ∧ ((11 ≠ 14) ∧ (11 ≠ 20)))))
theorem row4 : R4 := by
  have h_0 : (8 ≠ 25) := by decide
  have h_1 : (8 ≠ 36) := by decide
  have h_2 : (8 ≠ 42) := by decide
  have h_3 : (8 ≠ 27) := by decide
  have h_4 : (8 ≠ 38) := by decide
  have h_5 : (8 ≠ 44) := by decide
  have h_6 : (8 ≠ 47) := by decide
  have h_7 : (11 ≠ 17) := by decide
  have h_8 : (11 ≠ 28) := by decide
  have h_9 : (11 ≠ 9) := by decide
  have h_10 : (11 ≠ 12) := by decide
  have h_11 : (11 ≠ 18) := by decide
  have h_12 : (11 ≠ 29) := by decide
  have h_13 : (11 ≠ 14) := by decide
  have h_14 : (11 ≠ 20) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R5 : Prop := ((((11 ≠ 31) ∧ ((11 ≠ 23) ∧ (11 ≠ 34))) ∧ (((11 ≠ 40) ∧ (11 ≠ 10)) ∧ ((11 ≠ 13) ∧ (11 ≠ 19)))) ∧ ((((11 ≠ 30) ∧ (11 ≠ 15)) ∧ ((11 ≠ 21) ∧ (11 ≠ 32))) ∧ (((11 ≠ 24) ∧ (11 ≠ 35)) ∧ ((11 ≠ 41) ∧ (11 ≠ 16)))))
theorem row5 : R5 := by
  have h_0 : (11 ≠ 31) := by decide
  have h_1 : (11 ≠ 23) := by decide
  have h_2 : (11 ≠ 34) := by decide
  have h_3 : (11 ≠ 40) := by decide
  have h_4 : (11 ≠ 10) := by decide
  have h_5 : (11 ≠ 13) := by decide
  have h_6 : (11 ≠ 19) := by decide
  have h_7 : (11 ≠ 30) := by decide
  have h_8 : (11 ≠ 15) := by decide
  have h_9 : (11 ≠ 21) := by decide
  have h_10 : (11 ≠ 32) := by decide
  have h_11 : (11 ≠ 24) := by decide
  have h_12 : (11 ≠ 35) := by decide
  have h_13 : (11 ≠ 41) := by decide
  have h_14 : (11 ≠ 16) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R6 : Prop := ((((11 ≠ 22) ∧ ((11 ≠ 33) ∧ (11 ≠ 25))) ∧ (((11 ≠ 36) ∧ (11 ≠ 42)) ∧ ((11 ≠ 27) ∧ (11 ≠ 38)))) ∧ ((((11 ≠ 44) ∧ (11 ≠ 47)) ∧ ((17 ≠ 28) ∧ (17 ≠ 9))) ∧ (((17 ≠ 12) ∧ (17 ≠ 18)) ∧ ((17 ≠ 29) ∧ (17 ≠ 14)))))
theorem row6 : R6 := by
  have h_0 : (11 ≠ 22) := by decide
  have h_1 : (11 ≠ 33) := by decide
  have h_2 : (11 ≠ 25) := by decide
  have h_3 : (11 ≠ 36) := by decide
  have h_4 : (11 ≠ 42) := by decide
  have h_5 : (11 ≠ 27) := by decide
  have h_6 : (11 ≠ 38) := by decide
  have h_7 : (11 ≠ 44) := by decide
  have h_8 : (11 ≠ 47) := by decide
  have h_9 : (17 ≠ 28) := by decide
  have h_10 : (17 ≠ 9) := by decide
  have h_11 : (17 ≠ 12) := by decide
  have h_12 : (17 ≠ 18) := by decide
  have h_13 : (17 ≠ 29) := by decide
  have h_14 : (17 ≠ 14) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R7 : Prop := ((((17 ≠ 20) ∧ ((17 ≠ 31) ∧ (17 ≠ 23))) ∧ (((17 ≠ 34) ∧ (17 ≠ 40)) ∧ ((17 ≠ 10) ∧ (17 ≠ 13)))) ∧ ((((17 ≠ 19) ∧ (17 ≠ 30)) ∧ ((17 ≠ 15) ∧ (17 ≠ 21))) ∧ (((17 ≠ 32) ∧ (17 ≠ 24)) ∧ ((17 ≠ 35) ∧ (17 ≠ 41)))))
theorem row7 : R7 := by
  have h_0 : (17 ≠ 20) := by decide
  have h_1 : (17 ≠ 31) := by decide
  have h_2 : (17 ≠ 23) := by decide
  have h_3 : (17 ≠ 34) := by decide
  have h_4 : (17 ≠ 40) := by decide
  have h_5 : (17 ≠ 10) := by decide
  have h_6 : (17 ≠ 13) := by decide
  have h_7 : (17 ≠ 19) := by decide
  have h_8 : (17 ≠ 30) := by decide
  have h_9 : (17 ≠ 15) := by decide
  have h_10 : (17 ≠ 21) := by decide
  have h_11 : (17 ≠ 32) := by decide
  have h_12 : (17 ≠ 24) := by decide
  have h_13 : (17 ≠ 35) := by decide
  have h_14 : (17 ≠ 41) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R8 : Prop := ((((17 ≠ 16) ∧ ((17 ≠ 22) ∧ (17 ≠ 33))) ∧ (((17 ≠ 25) ∧ (17 ≠ 36)) ∧ ((17 ≠ 42) ∧ (17 ≠ 27)))) ∧ ((((17 ≠ 38) ∧ (17 ≠ 44)) ∧ ((17 ≠ 47) ∧ (28 ≠ 9))) ∧ (((28 ≠ 12) ∧ (28 ≠ 18)) ∧ ((28 ≠ 29) ∧ (28 ≠ 14)))))
theorem row8 : R8 := by
  have h_0 : (17 ≠ 16) := by decide
  have h_1 : (17 ≠ 22) := by decide
  have h_2 : (17 ≠ 33) := by decide
  have h_3 : (17 ≠ 25) := by decide
  have h_4 : (17 ≠ 36) := by decide
  have h_5 : (17 ≠ 42) := by decide
  have h_6 : (17 ≠ 27) := by decide
  have h_7 : (17 ≠ 38) := by decide
  have h_8 : (17 ≠ 44) := by decide
  have h_9 : (17 ≠ 47) := by decide
  have h_10 : (28 ≠ 9) := by decide
  have h_11 : (28 ≠ 12) := by decide
  have h_12 : (28 ≠ 18) := by decide
  have h_13 : (28 ≠ 29) := by decide
  have h_14 : (28 ≠ 14) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R9 : Prop := ((((28 ≠ 20) ∧ ((28 ≠ 31) ∧ (28 ≠ 23))) ∧ (((28 ≠ 34) ∧ (28 ≠ 40)) ∧ ((28 ≠ 10) ∧ (28 ≠ 13)))) ∧ ((((28 ≠ 19) ∧ (28 ≠ 30)) ∧ ((28 ≠ 15) ∧ (28 ≠ 21))) ∧ (((28 ≠ 32) ∧ (28 ≠ 24)) ∧ ((28 ≠ 35) ∧ (28 ≠ 41)))))
theorem row9 : R9 := by
  have h_0 : (28 ≠ 20) := by decide
  have h_1 : (28 ≠ 31) := by decide
  have h_2 : (28 ≠ 23) := by decide
  have h_3 : (28 ≠ 34) := by decide
  have h_4 : (28 ≠ 40) := by decide
  have h_5 : (28 ≠ 10) := by decide
  have h_6 : (28 ≠ 13) := by decide
  have h_7 : (28 ≠ 19) := by decide
  have h_8 : (28 ≠ 30) := by decide
  have h_9 : (28 ≠ 15) := by decide
  have h_10 : (28 ≠ 21) := by decide
  have h_11 : (28 ≠ 32) := by decide
  have h_12 : (28 ≠ 24) := by decide
  have h_13 : (28 ≠ 35) := by decide
  have h_14 : (28 ≠ 41) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R10 : Prop := ((((28 ≠ 16) ∧ ((28 ≠ 22) ∧ (28 ≠ 33))) ∧ (((28 ≠ 25) ∧ (28 ≠ 36)) ∧ ((28 ≠ 42) ∧ (28 ≠ 27)))) ∧ ((((28 ≠ 38) ∧ (28 ≠ 44)) ∧ ((28 ≠ 47) ∧ (9 ≠ 12))) ∧ (((9 ≠ 18) ∧ (9 ≠ 29)) ∧ ((9 ≠ 14) ∧ (9 ≠ 20)))))
theorem row10 : R10 := by
  have h_0 : (28 ≠ 16) := by decide
  have h_1 : (28 ≠ 22) := by decide
  have h_2 : (28 ≠ 33) := by decide
  have h_3 : (28 ≠ 25) := by decide
  have h_4 : (28 ≠ 36) := by decide
  have h_5 : (28 ≠ 42) := by decide
  have h_6 : (28 ≠ 27) := by decide
  have h_7 : (28 ≠ 38) := by decide
  have h_8 : (28 ≠ 44) := by decide
  have h_9 : (28 ≠ 47) := by decide
  have h_10 : (9 ≠ 12) := by decide
  have h_11 : (9 ≠ 18) := by decide
  have h_12 : (9 ≠ 29) := by decide
  have h_13 : (9 ≠ 14) := by decide
  have h_14 : (9 ≠ 20) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R11 : Prop := ((((9 ≠ 31) ∧ ((9 ≠ 23) ∧ (9 ≠ 34))) ∧ (((9 ≠ 40) ∧ (9 ≠ 10)) ∧ ((9 ≠ 13) ∧ (9 ≠ 19)))) ∧ ((((9 ≠ 30) ∧ (9 ≠ 15)) ∧ ((9 ≠ 21) ∧ (9 ≠ 32))) ∧ (((9 ≠ 24) ∧ (9 ≠ 35)) ∧ ((9 ≠ 41) ∧ (9 ≠ 16)))))
theorem row11 : R11 := by
  have h_0 : (9 ≠ 31) := by decide
  have h_1 : (9 ≠ 23) := by decide
  have h_2 : (9 ≠ 34) := by decide
  have h_3 : (9 ≠ 40) := by decide
  have h_4 : (9 ≠ 10) := by decide
  have h_5 : (9 ≠ 13) := by decide
  have h_6 : (9 ≠ 19) := by decide
  have h_7 : (9 ≠ 30) := by decide
  have h_8 : (9 ≠ 15) := by decide
  have h_9 : (9 ≠ 21) := by decide
  have h_10 : (9 ≠ 32) := by decide
  have h_11 : (9 ≠ 24) := by decide
  have h_12 : (9 ≠ 35) := by decide
  have h_13 : (9 ≠ 41) := by decide
  have h_14 : (9 ≠ 16) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R12 : Prop := ((((9 ≠ 22) ∧ ((9 ≠ 33) ∧ (9 ≠ 25))) ∧ (((9 ≠ 36) ∧ (9 ≠ 42)) ∧ ((9 ≠ 27) ∧ (9 ≠ 38)))) ∧ ((((9 ≠ 44) ∧ (9 ≠ 47)) ∧ ((12 ≠ 18) ∧ (12 ≠ 29))) ∧ (((12 ≠ 14) ∧ (12 ≠ 20)) ∧ ((12 ≠ 31) ∧ (12 ≠ 23)))))
theorem row12 : R12 := by
  have h_0 : (9 ≠ 22) := by decide
  have h_1 : (9 ≠ 33) := by decide
  have h_2 : (9 ≠ 25) := by decide
  have h_3 : (9 ≠ 36) := by decide
  have h_4 : (9 ≠ 42) := by decide
  have h_5 : (9 ≠ 27) := by decide
  have h_6 : (9 ≠ 38) := by decide
  have h_7 : (9 ≠ 44) := by decide
  have h_8 : (9 ≠ 47) := by decide
  have h_9 : (12 ≠ 18) := by decide
  have h_10 : (12 ≠ 29) := by decide
  have h_11 : (12 ≠ 14) := by decide
  have h_12 : (12 ≠ 20) := by decide
  have h_13 : (12 ≠ 31) := by decide
  have h_14 : (12 ≠ 23) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R13 : Prop := ((((12 ≠ 34) ∧ ((12 ≠ 40) ∧ (12 ≠ 10))) ∧ (((12 ≠ 13) ∧ (12 ≠ 19)) ∧ ((12 ≠ 30) ∧ (12 ≠ 15)))) ∧ ((((12 ≠ 21) ∧ (12 ≠ 32)) ∧ ((12 ≠ 24) ∧ (12 ≠ 35))) ∧ (((12 ≠ 41) ∧ (12 ≠ 16)) ∧ ((12 ≠ 22) ∧ (12 ≠ 33)))))
theorem row13 : R13 := by
  have h_0 : (12 ≠ 34) := by decide
  have h_1 : (12 ≠ 40) := by decide
  have h_2 : (12 ≠ 10) := by decide
  have h_3 : (12 ≠ 13) := by decide
  have h_4 : (12 ≠ 19) := by decide
  have h_5 : (12 ≠ 30) := by decide
  have h_6 : (12 ≠ 15) := by decide
  have h_7 : (12 ≠ 21) := by decide
  have h_8 : (12 ≠ 32) := by decide
  have h_9 : (12 ≠ 24) := by decide
  have h_10 : (12 ≠ 35) := by decide
  have h_11 : (12 ≠ 41) := by decide
  have h_12 : (12 ≠ 16) := by decide
  have h_13 : (12 ≠ 22) := by decide
  have h_14 : (12 ≠ 33) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R14 : Prop := ((((12 ≠ 25) ∧ ((12 ≠ 36) ∧ (12 ≠ 42))) ∧ (((12 ≠ 27) ∧ (12 ≠ 38)) ∧ ((12 ≠ 44) ∧ (12 ≠ 47)))) ∧ ((((18 ≠ 29) ∧ (18 ≠ 14)) ∧ ((18 ≠ 20) ∧ (18 ≠ 31))) ∧ (((18 ≠ 23) ∧ (18 ≠ 34)) ∧ ((18 ≠ 40) ∧ (18 ≠ 10)))))
theorem row14 : R14 := by
  have h_0 : (12 ≠ 25) := by decide
  have h_1 : (12 ≠ 36) := by decide
  have h_2 : (12 ≠ 42) := by decide
  have h_3 : (12 ≠ 27) := by decide
  have h_4 : (12 ≠ 38) := by decide
  have h_5 : (12 ≠ 44) := by decide
  have h_6 : (12 ≠ 47) := by decide
  have h_7 : (18 ≠ 29) := by decide
  have h_8 : (18 ≠ 14) := by decide
  have h_9 : (18 ≠ 20) := by decide
  have h_10 : (18 ≠ 31) := by decide
  have h_11 : (18 ≠ 23) := by decide
  have h_12 : (18 ≠ 34) := by decide
  have h_13 : (18 ≠ 40) := by decide
  have h_14 : (18 ≠ 10) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R15 : Prop := ((((18 ≠ 13) ∧ ((18 ≠ 19) ∧ (18 ≠ 30))) ∧ (((18 ≠ 15) ∧ (18 ≠ 21)) ∧ ((18 ≠ 32) ∧ (18 ≠ 24)))) ∧ ((((18 ≠ 35) ∧ (18 ≠ 41)) ∧ ((18 ≠ 16) ∧ (18 ≠ 22))) ∧ (((18 ≠ 33) ∧ (18 ≠ 25)) ∧ ((18 ≠ 36) ∧ (18 ≠ 42)))))
theorem row15 : R15 := by
  have h_0 : (18 ≠ 13) := by decide
  have h_1 : (18 ≠ 19) := by decide
  have h_2 : (18 ≠ 30) := by decide
  have h_3 : (18 ≠ 15) := by decide
  have h_4 : (18 ≠ 21) := by decide
  have h_5 : (18 ≠ 32) := by decide
  have h_6 : (18 ≠ 24) := by decide
  have h_7 : (18 ≠ 35) := by decide
  have h_8 : (18 ≠ 41) := by decide
  have h_9 : (18 ≠ 16) := by decide
  have h_10 : (18 ≠ 22) := by decide
  have h_11 : (18 ≠ 33) := by decide
  have h_12 : (18 ≠ 25) := by decide
  have h_13 : (18 ≠ 36) := by decide
  have h_14 : (18 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R16 : Prop := ((((18 ≠ 27) ∧ ((18 ≠ 38) ∧ (18 ≠ 44))) ∧ (((18 ≠ 47) ∧ (29 ≠ 14)) ∧ ((29 ≠ 20) ∧ (29 ≠ 31)))) ∧ ((((29 ≠ 23) ∧ (29 ≠ 34)) ∧ ((29 ≠ 40) ∧ (29 ≠ 10))) ∧ (((29 ≠ 13) ∧ (29 ≠ 19)) ∧ ((29 ≠ 30) ∧ (29 ≠ 15)))))
theorem row16 : R16 := by
  have h_0 : (18 ≠ 27) := by decide
  have h_1 : (18 ≠ 38) := by decide
  have h_2 : (18 ≠ 44) := by decide
  have h_3 : (18 ≠ 47) := by decide
  have h_4 : (29 ≠ 14) := by decide
  have h_5 : (29 ≠ 20) := by decide
  have h_6 : (29 ≠ 31) := by decide
  have h_7 : (29 ≠ 23) := by decide
  have h_8 : (29 ≠ 34) := by decide
  have h_9 : (29 ≠ 40) := by decide
  have h_10 : (29 ≠ 10) := by decide
  have h_11 : (29 ≠ 13) := by decide
  have h_12 : (29 ≠ 19) := by decide
  have h_13 : (29 ≠ 30) := by decide
  have h_14 : (29 ≠ 15) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R17 : Prop := ((((29 ≠ 21) ∧ ((29 ≠ 32) ∧ (29 ≠ 24))) ∧ (((29 ≠ 35) ∧ (29 ≠ 41)) ∧ ((29 ≠ 16) ∧ (29 ≠ 22)))) ∧ ((((29 ≠ 33) ∧ (29 ≠ 25)) ∧ ((29 ≠ 36) ∧ (29 ≠ 42))) ∧ (((29 ≠ 27) ∧ (29 ≠ 38)) ∧ ((29 ≠ 44) ∧ (29 ≠ 47)))))
theorem row17 : R17 := by
  have h_0 : (29 ≠ 21) := by decide
  have h_1 : (29 ≠ 32) := by decide
  have h_2 : (29 ≠ 24) := by decide
  have h_3 : (29 ≠ 35) := by decide
  have h_4 : (29 ≠ 41) := by decide
  have h_5 : (29 ≠ 16) := by decide
  have h_6 : (29 ≠ 22) := by decide
  have h_7 : (29 ≠ 33) := by decide
  have h_8 : (29 ≠ 25) := by decide
  have h_9 : (29 ≠ 36) := by decide
  have h_10 : (29 ≠ 42) := by decide
  have h_11 : (29 ≠ 27) := by decide
  have h_12 : (29 ≠ 38) := by decide
  have h_13 : (29 ≠ 44) := by decide
  have h_14 : (29 ≠ 47) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R18 : Prop := ((((14 ≠ 20) ∧ ((14 ≠ 31) ∧ (14 ≠ 23))) ∧ (((14 ≠ 34) ∧ (14 ≠ 40)) ∧ ((14 ≠ 10) ∧ (14 ≠ 13)))) ∧ ((((14 ≠ 19) ∧ (14 ≠ 30)) ∧ ((14 ≠ 15) ∧ (14 ≠ 21))) ∧ (((14 ≠ 32) ∧ (14 ≠ 24)) ∧ ((14 ≠ 35) ∧ (14 ≠ 41)))))
theorem row18 : R18 := by
  have h_0 : (14 ≠ 20) := by decide
  have h_1 : (14 ≠ 31) := by decide
  have h_2 : (14 ≠ 23) := by decide
  have h_3 : (14 ≠ 34) := by decide
  have h_4 : (14 ≠ 40) := by decide
  have h_5 : (14 ≠ 10) := by decide
  have h_6 : (14 ≠ 13) := by decide
  have h_7 : (14 ≠ 19) := by decide
  have h_8 : (14 ≠ 30) := by decide
  have h_9 : (14 ≠ 15) := by decide
  have h_10 : (14 ≠ 21) := by decide
  have h_11 : (14 ≠ 32) := by decide
  have h_12 : (14 ≠ 24) := by decide
  have h_13 : (14 ≠ 35) := by decide
  have h_14 : (14 ≠ 41) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R19 : Prop := ((((14 ≠ 16) ∧ ((14 ≠ 22) ∧ (14 ≠ 33))) ∧ (((14 ≠ 25) ∧ (14 ≠ 36)) ∧ ((14 ≠ 42) ∧ (14 ≠ 27)))) ∧ ((((14 ≠ 38) ∧ (14 ≠ 44)) ∧ ((14 ≠ 47) ∧ (20 ≠ 31))) ∧ (((20 ≠ 23) ∧ (20 ≠ 34)) ∧ ((20 ≠ 40) ∧ (20 ≠ 10)))))
theorem row19 : R19 := by
  have h_0 : (14 ≠ 16) := by decide
  have h_1 : (14 ≠ 22) := by decide
  have h_2 : (14 ≠ 33) := by decide
  have h_3 : (14 ≠ 25) := by decide
  have h_4 : (14 ≠ 36) := by decide
  have h_5 : (14 ≠ 42) := by decide
  have h_6 : (14 ≠ 27) := by decide
  have h_7 : (14 ≠ 38) := by decide
  have h_8 : (14 ≠ 44) := by decide
  have h_9 : (14 ≠ 47) := by decide
  have h_10 : (20 ≠ 31) := by decide
  have h_11 : (20 ≠ 23) := by decide
  have h_12 : (20 ≠ 34) := by decide
  have h_13 : (20 ≠ 40) := by decide
  have h_14 : (20 ≠ 10) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R20 : Prop := ((((20 ≠ 13) ∧ ((20 ≠ 19) ∧ (20 ≠ 30))) ∧ (((20 ≠ 15) ∧ (20 ≠ 21)) ∧ ((20 ≠ 32) ∧ (20 ≠ 24)))) ∧ ((((20 ≠ 35) ∧ (20 ≠ 41)) ∧ ((20 ≠ 16) ∧ (20 ≠ 22))) ∧ (((20 ≠ 33) ∧ (20 ≠ 25)) ∧ ((20 ≠ 36) ∧ (20 ≠ 42)))))
theorem row20 : R20 := by
  have h_0 : (20 ≠ 13) := by decide
  have h_1 : (20 ≠ 19) := by decide
  have h_2 : (20 ≠ 30) := by decide
  have h_3 : (20 ≠ 15) := by decide
  have h_4 : (20 ≠ 21) := by decide
  have h_5 : (20 ≠ 32) := by decide
  have h_6 : (20 ≠ 24) := by decide
  have h_7 : (20 ≠ 35) := by decide
  have h_8 : (20 ≠ 41) := by decide
  have h_9 : (20 ≠ 16) := by decide
  have h_10 : (20 ≠ 22) := by decide
  have h_11 : (20 ≠ 33) := by decide
  have h_12 : (20 ≠ 25) := by decide
  have h_13 : (20 ≠ 36) := by decide
  have h_14 : (20 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R21 : Prop := ((((20 ≠ 27) ∧ ((20 ≠ 38) ∧ (20 ≠ 44))) ∧ (((20 ≠ 47) ∧ (31 ≠ 23)) ∧ ((31 ≠ 34) ∧ (31 ≠ 40)))) ∧ ((((31 ≠ 10) ∧ (31 ≠ 13)) ∧ ((31 ≠ 19) ∧ (31 ≠ 30))) ∧ (((31 ≠ 15) ∧ (31 ≠ 21)) ∧ ((31 ≠ 32) ∧ (31 ≠ 24)))))
theorem row21 : R21 := by
  have h_0 : (20 ≠ 27) := by decide
  have h_1 : (20 ≠ 38) := by decide
  have h_2 : (20 ≠ 44) := by decide
  have h_3 : (20 ≠ 47) := by decide
  have h_4 : (31 ≠ 23) := by decide
  have h_5 : (31 ≠ 34) := by decide
  have h_6 : (31 ≠ 40) := by decide
  have h_7 : (31 ≠ 10) := by decide
  have h_8 : (31 ≠ 13) := by decide
  have h_9 : (31 ≠ 19) := by decide
  have h_10 : (31 ≠ 30) := by decide
  have h_11 : (31 ≠ 15) := by decide
  have h_12 : (31 ≠ 21) := by decide
  have h_13 : (31 ≠ 32) := by decide
  have h_14 : (31 ≠ 24) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R22 : Prop := ((((31 ≠ 35) ∧ ((31 ≠ 41) ∧ (31 ≠ 16))) ∧ (((31 ≠ 22) ∧ (31 ≠ 33)) ∧ ((31 ≠ 25) ∧ (31 ≠ 36)))) ∧ ((((31 ≠ 42) ∧ (31 ≠ 27)) ∧ ((31 ≠ 38) ∧ (31 ≠ 44))) ∧ (((31 ≠ 47) ∧ (23 ≠ 34)) ∧ ((23 ≠ 40) ∧ (23 ≠ 10)))))
theorem row22 : R22 := by
  have h_0 : (31 ≠ 35) := by decide
  have h_1 : (31 ≠ 41) := by decide
  have h_2 : (31 ≠ 16) := by decide
  have h_3 : (31 ≠ 22) := by decide
  have h_4 : (31 ≠ 33) := by decide
  have h_5 : (31 ≠ 25) := by decide
  have h_6 : (31 ≠ 36) := by decide
  have h_7 : (31 ≠ 42) := by decide
  have h_8 : (31 ≠ 27) := by decide
  have h_9 : (31 ≠ 38) := by decide
  have h_10 : (31 ≠ 44) := by decide
  have h_11 : (31 ≠ 47) := by decide
  have h_12 : (23 ≠ 34) := by decide
  have h_13 : (23 ≠ 40) := by decide
  have h_14 : (23 ≠ 10) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R23 : Prop := ((((23 ≠ 13) ∧ ((23 ≠ 19) ∧ (23 ≠ 30))) ∧ (((23 ≠ 15) ∧ (23 ≠ 21)) ∧ ((23 ≠ 32) ∧ (23 ≠ 24)))) ∧ ((((23 ≠ 35) ∧ (23 ≠ 41)) ∧ ((23 ≠ 16) ∧ (23 ≠ 22))) ∧ (((23 ≠ 33) ∧ (23 ≠ 25)) ∧ ((23 ≠ 36) ∧ (23 ≠ 42)))))
theorem row23 : R23 := by
  have h_0 : (23 ≠ 13) := by decide
  have h_1 : (23 ≠ 19) := by decide
  have h_2 : (23 ≠ 30) := by decide
  have h_3 : (23 ≠ 15) := by decide
  have h_4 : (23 ≠ 21) := by decide
  have h_5 : (23 ≠ 32) := by decide
  have h_6 : (23 ≠ 24) := by decide
  have h_7 : (23 ≠ 35) := by decide
  have h_8 : (23 ≠ 41) := by decide
  have h_9 : (23 ≠ 16) := by decide
  have h_10 : (23 ≠ 22) := by decide
  have h_11 : (23 ≠ 33) := by decide
  have h_12 : (23 ≠ 25) := by decide
  have h_13 : (23 ≠ 36) := by decide
  have h_14 : (23 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R24 : Prop := ((((23 ≠ 27) ∧ ((23 ≠ 38) ∧ (23 ≠ 44))) ∧ (((23 ≠ 47) ∧ (34 ≠ 40)) ∧ ((34 ≠ 10) ∧ (34 ≠ 13)))) ∧ ((((34 ≠ 19) ∧ (34 ≠ 30)) ∧ ((34 ≠ 15) ∧ (34 ≠ 21))) ∧ (((34 ≠ 32) ∧ (34 ≠ 24)) ∧ ((34 ≠ 35) ∧ (34 ≠ 41)))))
theorem row24 : R24 := by
  have h_0 : (23 ≠ 27) := by decide
  have h_1 : (23 ≠ 38) := by decide
  have h_2 : (23 ≠ 44) := by decide
  have h_3 : (23 ≠ 47) := by decide
  have h_4 : (34 ≠ 40) := by decide
  have h_5 : (34 ≠ 10) := by decide
  have h_6 : (34 ≠ 13) := by decide
  have h_7 : (34 ≠ 19) := by decide
  have h_8 : (34 ≠ 30) := by decide
  have h_9 : (34 ≠ 15) := by decide
  have h_10 : (34 ≠ 21) := by decide
  have h_11 : (34 ≠ 32) := by decide
  have h_12 : (34 ≠ 24) := by decide
  have h_13 : (34 ≠ 35) := by decide
  have h_14 : (34 ≠ 41) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R25 : Prop := ((((34 ≠ 16) ∧ ((34 ≠ 22) ∧ (34 ≠ 33))) ∧ (((34 ≠ 25) ∧ (34 ≠ 36)) ∧ ((34 ≠ 42) ∧ (34 ≠ 27)))) ∧ ((((34 ≠ 38) ∧ (34 ≠ 44)) ∧ ((34 ≠ 47) ∧ (40 ≠ 10))) ∧ (((40 ≠ 13) ∧ (40 ≠ 19)) ∧ ((40 ≠ 30) ∧ (40 ≠ 15)))))
theorem row25 : R25 := by
  have h_0 : (34 ≠ 16) := by decide
  have h_1 : (34 ≠ 22) := by decide
  have h_2 : (34 ≠ 33) := by decide
  have h_3 : (34 ≠ 25) := by decide
  have h_4 : (34 ≠ 36) := by decide
  have h_5 : (34 ≠ 42) := by decide
  have h_6 : (34 ≠ 27) := by decide
  have h_7 : (34 ≠ 38) := by decide
  have h_8 : (34 ≠ 44) := by decide
  have h_9 : (34 ≠ 47) := by decide
  have h_10 : (40 ≠ 10) := by decide
  have h_11 : (40 ≠ 13) := by decide
  have h_12 : (40 ≠ 19) := by decide
  have h_13 : (40 ≠ 30) := by decide
  have h_14 : (40 ≠ 15) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R26 : Prop := ((((40 ≠ 21) ∧ ((40 ≠ 32) ∧ (40 ≠ 24))) ∧ (((40 ≠ 35) ∧ (40 ≠ 41)) ∧ ((40 ≠ 16) ∧ (40 ≠ 22)))) ∧ ((((40 ≠ 33) ∧ (40 ≠ 25)) ∧ ((40 ≠ 36) ∧ (40 ≠ 42))) ∧ (((40 ≠ 27) ∧ (40 ≠ 38)) ∧ ((40 ≠ 44) ∧ (40 ≠ 47)))))
theorem row26 : R26 := by
  have h_0 : (40 ≠ 21) := by decide
  have h_1 : (40 ≠ 32) := by decide
  have h_2 : (40 ≠ 24) := by decide
  have h_3 : (40 ≠ 35) := by decide
  have h_4 : (40 ≠ 41) := by decide
  have h_5 : (40 ≠ 16) := by decide
  have h_6 : (40 ≠ 22) := by decide
  have h_7 : (40 ≠ 33) := by decide
  have h_8 : (40 ≠ 25) := by decide
  have h_9 : (40 ≠ 36) := by decide
  have h_10 : (40 ≠ 42) := by decide
  have h_11 : (40 ≠ 27) := by decide
  have h_12 : (40 ≠ 38) := by decide
  have h_13 : (40 ≠ 44) := by decide
  have h_14 : (40 ≠ 47) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R27 : Prop := ((((10 ≠ 13) ∧ ((10 ≠ 19) ∧ (10 ≠ 30))) ∧ (((10 ≠ 15) ∧ (10 ≠ 21)) ∧ ((10 ≠ 32) ∧ (10 ≠ 24)))) ∧ ((((10 ≠ 35) ∧ (10 ≠ 41)) ∧ ((10 ≠ 16) ∧ (10 ≠ 22))) ∧ (((10 ≠ 33) ∧ (10 ≠ 25)) ∧ ((10 ≠ 36) ∧ (10 ≠ 42)))))
theorem row27 : R27 := by
  have h_0 : (10 ≠ 13) := by decide
  have h_1 : (10 ≠ 19) := by decide
  have h_2 : (10 ≠ 30) := by decide
  have h_3 : (10 ≠ 15) := by decide
  have h_4 : (10 ≠ 21) := by decide
  have h_5 : (10 ≠ 32) := by decide
  have h_6 : (10 ≠ 24) := by decide
  have h_7 : (10 ≠ 35) := by decide
  have h_8 : (10 ≠ 41) := by decide
  have h_9 : (10 ≠ 16) := by decide
  have h_10 : (10 ≠ 22) := by decide
  have h_11 : (10 ≠ 33) := by decide
  have h_12 : (10 ≠ 25) := by decide
  have h_13 : (10 ≠ 36) := by decide
  have h_14 : (10 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R28 : Prop := ((((10 ≠ 27) ∧ ((10 ≠ 38) ∧ (10 ≠ 44))) ∧ (((10 ≠ 47) ∧ (13 ≠ 19)) ∧ ((13 ≠ 30) ∧ (13 ≠ 15)))) ∧ ((((13 ≠ 21) ∧ (13 ≠ 32)) ∧ ((13 ≠ 24) ∧ (13 ≠ 35))) ∧ (((13 ≠ 41) ∧ (13 ≠ 16)) ∧ ((13 ≠ 22) ∧ (13 ≠ 33)))))
theorem row28 : R28 := by
  have h_0 : (10 ≠ 27) := by decide
  have h_1 : (10 ≠ 38) := by decide
  have h_2 : (10 ≠ 44) := by decide
  have h_3 : (10 ≠ 47) := by decide
  have h_4 : (13 ≠ 19) := by decide
  have h_5 : (13 ≠ 30) := by decide
  have h_6 : (13 ≠ 15) := by decide
  have h_7 : (13 ≠ 21) := by decide
  have h_8 : (13 ≠ 32) := by decide
  have h_9 : (13 ≠ 24) := by decide
  have h_10 : (13 ≠ 35) := by decide
  have h_11 : (13 ≠ 41) := by decide
  have h_12 : (13 ≠ 16) := by decide
  have h_13 : (13 ≠ 22) := by decide
  have h_14 : (13 ≠ 33) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R29 : Prop := ((((13 ≠ 25) ∧ ((13 ≠ 36) ∧ (13 ≠ 42))) ∧ (((13 ≠ 27) ∧ (13 ≠ 38)) ∧ ((13 ≠ 44) ∧ (13 ≠ 47)))) ∧ ((((19 ≠ 30) ∧ (19 ≠ 15)) ∧ ((19 ≠ 21) ∧ (19 ≠ 32))) ∧ (((19 ≠ 24) ∧ (19 ≠ 35)) ∧ ((19 ≠ 41) ∧ (19 ≠ 16)))))
theorem row29 : R29 := by
  have h_0 : (13 ≠ 25) := by decide
  have h_1 : (13 ≠ 36) := by decide
  have h_2 : (13 ≠ 42) := by decide
  have h_3 : (13 ≠ 27) := by decide
  have h_4 : (13 ≠ 38) := by decide
  have h_5 : (13 ≠ 44) := by decide
  have h_6 : (13 ≠ 47) := by decide
  have h_7 : (19 ≠ 30) := by decide
  have h_8 : (19 ≠ 15) := by decide
  have h_9 : (19 ≠ 21) := by decide
  have h_10 : (19 ≠ 32) := by decide
  have h_11 : (19 ≠ 24) := by decide
  have h_12 : (19 ≠ 35) := by decide
  have h_13 : (19 ≠ 41) := by decide
  have h_14 : (19 ≠ 16) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R30 : Prop := ((((19 ≠ 22) ∧ ((19 ≠ 33) ∧ (19 ≠ 25))) ∧ (((19 ≠ 36) ∧ (19 ≠ 42)) ∧ ((19 ≠ 27) ∧ (19 ≠ 38)))) ∧ ((((19 ≠ 44) ∧ (19 ≠ 47)) ∧ ((30 ≠ 15) ∧ (30 ≠ 21))) ∧ (((30 ≠ 32) ∧ (30 ≠ 24)) ∧ ((30 ≠ 35) ∧ (30 ≠ 41)))))
theorem row30 : R30 := by
  have h_0 : (19 ≠ 22) := by decide
  have h_1 : (19 ≠ 33) := by decide
  have h_2 : (19 ≠ 25) := by decide
  have h_3 : (19 ≠ 36) := by decide
  have h_4 : (19 ≠ 42) := by decide
  have h_5 : (19 ≠ 27) := by decide
  have h_6 : (19 ≠ 38) := by decide
  have h_7 : (19 ≠ 44) := by decide
  have h_8 : (19 ≠ 47) := by decide
  have h_9 : (30 ≠ 15) := by decide
  have h_10 : (30 ≠ 21) := by decide
  have h_11 : (30 ≠ 32) := by decide
  have h_12 : (30 ≠ 24) := by decide
  have h_13 : (30 ≠ 35) := by decide
  have h_14 : (30 ≠ 41) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R31 : Prop := ((((30 ≠ 16) ∧ ((30 ≠ 22) ∧ (30 ≠ 33))) ∧ (((30 ≠ 25) ∧ (30 ≠ 36)) ∧ ((30 ≠ 42) ∧ (30 ≠ 27)))) ∧ ((((30 ≠ 38) ∧ (30 ≠ 44)) ∧ ((30 ≠ 47) ∧ (15 ≠ 21))) ∧ (((15 ≠ 32) ∧ (15 ≠ 24)) ∧ ((15 ≠ 35) ∧ (15 ≠ 41)))))
theorem row31 : R31 := by
  have h_0 : (30 ≠ 16) := by decide
  have h_1 : (30 ≠ 22) := by decide
  have h_2 : (30 ≠ 33) := by decide
  have h_3 : (30 ≠ 25) := by decide
  have h_4 : (30 ≠ 36) := by decide
  have h_5 : (30 ≠ 42) := by decide
  have h_6 : (30 ≠ 27) := by decide
  have h_7 : (30 ≠ 38) := by decide
  have h_8 : (30 ≠ 44) := by decide
  have h_9 : (30 ≠ 47) := by decide
  have h_10 : (15 ≠ 21) := by decide
  have h_11 : (15 ≠ 32) := by decide
  have h_12 : (15 ≠ 24) := by decide
  have h_13 : (15 ≠ 35) := by decide
  have h_14 : (15 ≠ 41) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R32 : Prop := ((((15 ≠ 16) ∧ ((15 ≠ 22) ∧ (15 ≠ 33))) ∧ (((15 ≠ 25) ∧ (15 ≠ 36)) ∧ ((15 ≠ 42) ∧ (15 ≠ 27)))) ∧ ((((15 ≠ 38) ∧ (15 ≠ 44)) ∧ ((15 ≠ 47) ∧ (21 ≠ 32))) ∧ (((21 ≠ 24) ∧ (21 ≠ 35)) ∧ ((21 ≠ 41) ∧ (21 ≠ 16)))))
theorem row32 : R32 := by
  have h_0 : (15 ≠ 16) := by decide
  have h_1 : (15 ≠ 22) := by decide
  have h_2 : (15 ≠ 33) := by decide
  have h_3 : (15 ≠ 25) := by decide
  have h_4 : (15 ≠ 36) := by decide
  have h_5 : (15 ≠ 42) := by decide
  have h_6 : (15 ≠ 27) := by decide
  have h_7 : (15 ≠ 38) := by decide
  have h_8 : (15 ≠ 44) := by decide
  have h_9 : (15 ≠ 47) := by decide
  have h_10 : (21 ≠ 32) := by decide
  have h_11 : (21 ≠ 24) := by decide
  have h_12 : (21 ≠ 35) := by decide
  have h_13 : (21 ≠ 41) := by decide
  have h_14 : (21 ≠ 16) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R33 : Prop := ((((21 ≠ 22) ∧ ((21 ≠ 33) ∧ (21 ≠ 25))) ∧ (((21 ≠ 36) ∧ (21 ≠ 42)) ∧ ((21 ≠ 27) ∧ (21 ≠ 38)))) ∧ ((((21 ≠ 44) ∧ (21 ≠ 47)) ∧ ((32 ≠ 24) ∧ (32 ≠ 35))) ∧ (((32 ≠ 41) ∧ (32 ≠ 16)) ∧ ((32 ≠ 22) ∧ (32 ≠ 33)))))
theorem row33 : R33 := by
  have h_0 : (21 ≠ 22) := by decide
  have h_1 : (21 ≠ 33) := by decide
  have h_2 : (21 ≠ 25) := by decide
  have h_3 : (21 ≠ 36) := by decide
  have h_4 : (21 ≠ 42) := by decide
  have h_5 : (21 ≠ 27) := by decide
  have h_6 : (21 ≠ 38) := by decide
  have h_7 : (21 ≠ 44) := by decide
  have h_8 : (21 ≠ 47) := by decide
  have h_9 : (32 ≠ 24) := by decide
  have h_10 : (32 ≠ 35) := by decide
  have h_11 : (32 ≠ 41) := by decide
  have h_12 : (32 ≠ 16) := by decide
  have h_13 : (32 ≠ 22) := by decide
  have h_14 : (32 ≠ 33) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R34 : Prop := ((((32 ≠ 25) ∧ ((32 ≠ 36) ∧ (32 ≠ 42))) ∧ (((32 ≠ 27) ∧ (32 ≠ 38)) ∧ ((32 ≠ 44) ∧ (32 ≠ 47)))) ∧ ((((24 ≠ 35) ∧ (24 ≠ 41)) ∧ ((24 ≠ 16) ∧ (24 ≠ 22))) ∧ (((24 ≠ 33) ∧ (24 ≠ 25)) ∧ ((24 ≠ 36) ∧ (24 ≠ 42)))))
theorem row34 : R34 := by
  have h_0 : (32 ≠ 25) := by decide
  have h_1 : (32 ≠ 36) := by decide
  have h_2 : (32 ≠ 42) := by decide
  have h_3 : (32 ≠ 27) := by decide
  have h_4 : (32 ≠ 38) := by decide
  have h_5 : (32 ≠ 44) := by decide
  have h_6 : (32 ≠ 47) := by decide
  have h_7 : (24 ≠ 35) := by decide
  have h_8 : (24 ≠ 41) := by decide
  have h_9 : (24 ≠ 16) := by decide
  have h_10 : (24 ≠ 22) := by decide
  have h_11 : (24 ≠ 33) := by decide
  have h_12 : (24 ≠ 25) := by decide
  have h_13 : (24 ≠ 36) := by decide
  have h_14 : (24 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R35 : Prop := ((((24 ≠ 27) ∧ ((24 ≠ 38) ∧ (24 ≠ 44))) ∧ (((24 ≠ 47) ∧ (35 ≠ 41)) ∧ ((35 ≠ 16) ∧ (35 ≠ 22)))) ∧ ((((35 ≠ 33) ∧ (35 ≠ 25)) ∧ ((35 ≠ 36) ∧ (35 ≠ 42))) ∧ (((35 ≠ 27) ∧ (35 ≠ 38)) ∧ ((35 ≠ 44) ∧ (35 ≠ 47)))))
theorem row35 : R35 := by
  have h_0 : (24 ≠ 27) := by decide
  have h_1 : (24 ≠ 38) := by decide
  have h_2 : (24 ≠ 44) := by decide
  have h_3 : (24 ≠ 47) := by decide
  have h_4 : (35 ≠ 41) := by decide
  have h_5 : (35 ≠ 16) := by decide
  have h_6 : (35 ≠ 22) := by decide
  have h_7 : (35 ≠ 33) := by decide
  have h_8 : (35 ≠ 25) := by decide
  have h_9 : (35 ≠ 36) := by decide
  have h_10 : (35 ≠ 42) := by decide
  have h_11 : (35 ≠ 27) := by decide
  have h_12 : (35 ≠ 38) := by decide
  have h_13 : (35 ≠ 44) := by decide
  have h_14 : (35 ≠ 47) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R36 : Prop := ((((41 ≠ 16) ∧ ((41 ≠ 22) ∧ (41 ≠ 33))) ∧ (((41 ≠ 25) ∧ (41 ≠ 36)) ∧ ((41 ≠ 42) ∧ (41 ≠ 27)))) ∧ ((((41 ≠ 38) ∧ (41 ≠ 44)) ∧ ((41 ≠ 47) ∧ (16 ≠ 22))) ∧ (((16 ≠ 33) ∧ (16 ≠ 25)) ∧ ((16 ≠ 36) ∧ (16 ≠ 42)))))
theorem row36 : R36 := by
  have h_0 : (41 ≠ 16) := by decide
  have h_1 : (41 ≠ 22) := by decide
  have h_2 : (41 ≠ 33) := by decide
  have h_3 : (41 ≠ 25) := by decide
  have h_4 : (41 ≠ 36) := by decide
  have h_5 : (41 ≠ 42) := by decide
  have h_6 : (41 ≠ 27) := by decide
  have h_7 : (41 ≠ 38) := by decide
  have h_8 : (41 ≠ 44) := by decide
  have h_9 : (41 ≠ 47) := by decide
  have h_10 : (16 ≠ 22) := by decide
  have h_11 : (16 ≠ 33) := by decide
  have h_12 : (16 ≠ 25) := by decide
  have h_13 : (16 ≠ 36) := by decide
  have h_14 : (16 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R37 : Prop := ((((16 ≠ 27) ∧ ((16 ≠ 38) ∧ (16 ≠ 44))) ∧ (((16 ≠ 47) ∧ (22 ≠ 33)) ∧ ((22 ≠ 25) ∧ (22 ≠ 36)))) ∧ ((((22 ≠ 42) ∧ (22 ≠ 27)) ∧ ((22 ≠ 38) ∧ (22 ≠ 44))) ∧ (((22 ≠ 47) ∧ (33 ≠ 25)) ∧ ((33 ≠ 36) ∧ (33 ≠ 42)))))
theorem row37 : R37 := by
  have h_0 : (16 ≠ 27) := by decide
  have h_1 : (16 ≠ 38) := by decide
  have h_2 : (16 ≠ 44) := by decide
  have h_3 : (16 ≠ 47) := by decide
  have h_4 : (22 ≠ 33) := by decide
  have h_5 : (22 ≠ 25) := by decide
  have h_6 : (22 ≠ 36) := by decide
  have h_7 : (22 ≠ 42) := by decide
  have h_8 : (22 ≠ 27) := by decide
  have h_9 : (22 ≠ 38) := by decide
  have h_10 : (22 ≠ 44) := by decide
  have h_11 : (22 ≠ 47) := by decide
  have h_12 : (33 ≠ 25) := by decide
  have h_13 : (33 ≠ 36) := by decide
  have h_14 : (33 ≠ 42) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R38 : Prop := ((((33 ≠ 27) ∧ ((33 ≠ 38) ∧ (33 ≠ 44))) ∧ (((33 ≠ 47) ∧ (25 ≠ 36)) ∧ ((25 ≠ 42) ∧ (25 ≠ 27)))) ∧ ((((25 ≠ 38) ∧ (25 ≠ 44)) ∧ ((25 ≠ 47) ∧ (36 ≠ 42))) ∧ (((36 ≠ 27) ∧ (36 ≠ 38)) ∧ ((36 ≠ 44) ∧ (36 ≠ 47)))))
theorem row38 : R38 := by
  have h_0 : (33 ≠ 27) := by decide
  have h_1 : (33 ≠ 38) := by decide
  have h_2 : (33 ≠ 44) := by decide
  have h_3 : (33 ≠ 47) := by decide
  have h_4 : (25 ≠ 36) := by decide
  have h_5 : (25 ≠ 42) := by decide
  have h_6 : (25 ≠ 27) := by decide
  have h_7 : (25 ≠ 38) := by decide
  have h_8 : (25 ≠ 44) := by decide
  have h_9 : (25 ≠ 47) := by decide
  have h_10 : (36 ≠ 42) := by decide
  have h_11 : (36 ≠ 27) := by decide
  have h_12 : (36 ≠ 38) := by decide
  have h_13 : (36 ≠ 44) := by decide
  have h_14 : (36 ≠ 47) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R39 : Prop := ((((42 ≠ 27) ∧ (42 ≠ 38)) ∧ ((42 ≠ 44) ∧ ((42 ≠ 47) ∧ (27 ≠ 38)))) ∧ (((27 ≠ 44) ∧ (27 ≠ 47)) ∧ ((38 ≠ 44) ∧ ((38 ≠ 47) ∧ (44 ≠ 47)))))
theorem row39 : R39 := by
  have h_0 : (42 ≠ 27) := by decide
  have h_1 : (42 ≠ 38) := by decide
  have h_2 : (42 ≠ 44) := by decide
  have h_3 : (42 ≠ 47) := by decide
  have h_4 : (27 ≠ 38) := by decide
  have h_5 : (27 ≠ 44) := by decide
  have h_6 : (27 ≠ 47) := by decide
  have h_7 : (38 ≠ 44) := by decide
  have h_8 : (38 ≠ 47) := by decide
  have h_9 : (44 ≠ 47) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, h_6⟩, ⟨h_7, ⟨h_8, h_9⟩⟩⟩⟩

theorem jsp212 :
  (((((R0 ∧ R1) ∧ (R2 ∧ (R3 ∧ R4))) ∧ ((R5 ∧ R6) ∧ (R7 ∧ (R8 ∧ R9)))) ∧ (((R10 ∧ R11) ∧ (R12 ∧ (R13 ∧ R14))) ∧ ((R15 ∧ R16) ∧ (R17 ∧ (R18 ∧ R19))))) ∧ ((((R20 ∧ R21) ∧ (R22 ∧ (R23 ∧ R24))) ∧ ((R25 ∧ R26) ∧ (R27 ∧ (R28 ∧ R29)))) ∧ (((R30 ∧ R31) ∧ (R32 ∧ (R33 ∧ R34))) ∧ ((R35 ∧ R36) ∧ (R37 ∧ (R38 ∧ R39)))))) := by
  exact ⟨⟨⟨⟨⟨row0, row1⟩, ⟨row2, ⟨row3, row4⟩⟩⟩, ⟨⟨row5, row6⟩, ⟨row7, ⟨row8, row9⟩⟩⟩⟩, ⟨⟨⟨row10, row11⟩, ⟨row12, ⟨row13, row14⟩⟩⟩, ⟨⟨row15, row16⟩, ⟨row17, ⟨row18, row19⟩⟩⟩⟩⟩, ⟨⟨⟨⟨row20, row21⟩, ⟨row22, ⟨row23, row24⟩⟩⟩, ⟨⟨row25, row26⟩, ⟨row27, ⟨row28, row29⟩⟩⟩⟩, ⟨⟨⟨row30, row31⟩, ⟨row32, ⟨row33, row34⟩⟩⟩, ⟨⟨row35, row36⟩, ⟨row37, ⟨row38, row39⟩⟩⟩⟩⟩⟩
