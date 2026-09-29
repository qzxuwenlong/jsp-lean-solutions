-- =====================================================================
-- JSP-000295 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How long can an increasing integer sequence in a prescribed range
--       be if all sums of consecutive terms are distinct?
--       （给定范围内递增整数序列可以多长，若所有连续项之和互异？）
--
-- 构造：区间 [1,16] 的递增序列 A = (1, 2, 4, 8)（2 的幂，长度 4）。
--   所有连续子序列之和（共 C(4+1,2) = 10 个）：
--     1, 2, 4, 8, 3, 6, 12, 7, 14, 15，
--   两两互异（C(10,2) = 45 个不等断言）。
--   2 的幂的超递增性质保证连续和互异；此处逐对闭项机器核验。
--   全部 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp295.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((1 ≠ 3) ∧ ((1 ≠ 7) ∧ (1 ≠ 15))) ∧ (((1 ≠ 2) ∧ (1 ≠ 6)) ∧ ((1 ≠ 14) ∧ (1 ≠ 4)))) ∧ ((((1 ≠ 12) ∧ (1 ≠ 8)) ∧ ((3 ≠ 7) ∧ (3 ≠ 15))) ∧ (((3 ≠ 2) ∧ (3 ≠ 6)) ∧ ((3 ≠ 14) ∧ (3 ≠ 4)))))
theorem row0 : R0 := by
  have h_0 : (1 ≠ 3) := by decide
  have h_1 : (1 ≠ 7) := by decide
  have h_2 : (1 ≠ 15) := by decide
  have h_3 : (1 ≠ 2) := by decide
  have h_4 : (1 ≠ 6) := by decide
  have h_5 : (1 ≠ 14) := by decide
  have h_6 : (1 ≠ 4) := by decide
  have h_7 : (1 ≠ 12) := by decide
  have h_8 : (1 ≠ 8) := by decide
  have h_9 : (3 ≠ 7) := by decide
  have h_10 : (3 ≠ 15) := by decide
  have h_11 : (3 ≠ 2) := by decide
  have h_12 : (3 ≠ 6) := by decide
  have h_13 : (3 ≠ 14) := by decide
  have h_14 : (3 ≠ 4) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R1 : Prop := ((((3 ≠ 12) ∧ ((3 ≠ 8) ∧ (7 ≠ 15))) ∧ (((7 ≠ 2) ∧ (7 ≠ 6)) ∧ ((7 ≠ 14) ∧ (7 ≠ 4)))) ∧ ((((7 ≠ 12) ∧ (7 ≠ 8)) ∧ ((15 ≠ 2) ∧ (15 ≠ 6))) ∧ (((15 ≠ 14) ∧ (15 ≠ 4)) ∧ ((15 ≠ 12) ∧ (15 ≠ 8)))))
theorem row1 : R1 := by
  have h_0 : (3 ≠ 12) := by decide
  have h_1 : (3 ≠ 8) := by decide
  have h_2 : (7 ≠ 15) := by decide
  have h_3 : (7 ≠ 2) := by decide
  have h_4 : (7 ≠ 6) := by decide
  have h_5 : (7 ≠ 14) := by decide
  have h_6 : (7 ≠ 4) := by decide
  have h_7 : (7 ≠ 12) := by decide
  have h_8 : (7 ≠ 8) := by decide
  have h_9 : (15 ≠ 2) := by decide
  have h_10 : (15 ≠ 6) := by decide
  have h_11 : (15 ≠ 14) := by decide
  have h_12 : (15 ≠ 4) := by decide
  have h_13 : (15 ≠ 12) := by decide
  have h_14 : (15 ≠ 8) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R2 : Prop := ((((2 ≠ 6) ∧ ((2 ≠ 14) ∧ (2 ≠ 4))) ∧ (((2 ≠ 12) ∧ (2 ≠ 8)) ∧ ((6 ≠ 14) ∧ (6 ≠ 4)))) ∧ ((((6 ≠ 12) ∧ (6 ≠ 8)) ∧ ((14 ≠ 4) ∧ (14 ≠ 12))) ∧ (((14 ≠ 8) ∧ (4 ≠ 12)) ∧ ((4 ≠ 8) ∧ (12 ≠ 8)))))
theorem row2 : R2 := by
  have h_0 : (2 ≠ 6) := by decide
  have h_1 : (2 ≠ 14) := by decide
  have h_2 : (2 ≠ 4) := by decide
  have h_3 : (2 ≠ 12) := by decide
  have h_4 : (2 ≠ 8) := by decide
  have h_5 : (6 ≠ 14) := by decide
  have h_6 : (6 ≠ 4) := by decide
  have h_7 : (6 ≠ 12) := by decide
  have h_8 : (6 ≠ 8) := by decide
  have h_9 : (14 ≠ 4) := by decide
  have h_10 : (14 ≠ 12) := by decide
  have h_11 : (14 ≠ 8) := by decide
  have h_12 : (4 ≠ 12) := by decide
  have h_13 : (4 ≠ 8) := by decide
  have h_14 : (12 ≠ 8) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

theorem jsp295 :
  (R0 ∧ (R1 ∧ R2)) := by
  exact ⟨row0, ⟨row1, row2⟩⟩
