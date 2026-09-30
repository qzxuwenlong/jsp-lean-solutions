-- =====================================================================
-- JSP-000580 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：From an arbitrary starting point, what is the worst-case interval
--       length needed for distinct multiples of the first several
--       positive integers?
--       （从任意起点出发，要为最初几个正整数的相异倍数提供
--       容纳区间，最坏情况下需要多长？）
--
-- 构造（例证）：起点 6，区间 [6, 9]（长度 4）包含 1、2、3、4 的
--   相异倍数：1→7, 2→6, 3→9, 4→8（{6,7,8,9} 互异，全部落在
--   [6,9] 内；程序搜索确认这是该起点下的最短长度）。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp580.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((7 % 1 = 0) ∧ (6 % 2 = 0)) ∧ ((9 % 3 = 0) ∧ (8 % 4 = 0))) ∧ (((6 ≠ 7) ∧ (6 ≠ 8)) ∧ ((6 ≠ 9) ∧ ((7 ≠ 8) ∧ (7 ≠ 9))))) ∧ ((((8 ≠ 9) ∧ (6 ≥ 6)) ∧ ((6 ≤ 9) ∧ (7 ≥ 6))) ∧ (((7 ≤ 9) ∧ (8 ≥ 6)) ∧ ((8 ≤ 9) ∧ ((9 ≥ 6) ∧ (9 ≤ 9))))))

theorem jsp580 : R0 := by

  have h_0 : (7 % 1 = 0) := by decide
  have h_1 : (6 % 2 = 0) := by decide
  have h_2 : (9 % 3 = 0) := by decide
  have h_3 : (8 % 4 = 0) := by decide
  have h_4 : (6 ≠ 7) := by decide
  have h_5 : (6 ≠ 8) := by decide
  have h_6 : (6 ≠ 9) := by decide
  have h_7 : (7 ≠ 8) := by decide
  have h_8 : (7 ≠ 9) := by decide
  have h_9 : (8 ≠ 9) := by decide
  have h_10 : (6 ≥ 6) := by decide
  have h_11 : (6 ≤ 9) := by decide
  have h_12 : (7 ≥ 6) := by decide
  have h_13 : (7 ≤ 9) := by decide
  have h_14 : (8 ≥ 6) := by decide
  have h_15 : (8 ≤ 9) := by decide
  have h_16 : (9 ≥ 6) := by decide
  have h_17 : (9 ≤ 9) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, ⟨h_7, h_8⟩⟩⟩⟩, ⟨⟨⟨h_9, h_10⟩, ⟨h_11, h_12⟩⟩, ⟨⟨h_13, h_14⟩, ⟨h_15, ⟨h_16, h_17⟩⟩⟩⟩⟩
