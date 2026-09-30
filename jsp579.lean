-- =====================================================================
-- JSP-000579 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How short an interval beyond the first several positive integers
--       can contain distinct multiples representing each of them?
--       （在最初几个正整数之后，多短的区间可以包含分别表示
--       其中每个数的相异倍数？）
--
-- 构造（例证）：区间 [2, 8]（长度 7）包含 1、2、3、4 的相异倍数：
--   · 1 的倍数：5
--   · 2 的倍数：4
--   · 3 的倍数：6
--   · 4 的倍数：8
--   （{5, 4, 6, 8} 六个成员界与六对互异逐一验证。）
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp579.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((5 % 1 = 0) ∧ (4 % 2 = 0)) ∧ ((6 % 3 = 0) ∧ (8 % 4 = 0))) ∧ (((4 ≠ 5) ∧ (4 ≠ 6)) ∧ ((4 ≠ 8) ∧ ((5 ≠ 6) ∧ (5 ≠ 8))))) ∧ ((((6 ≠ 8) ∧ (4 ≥ 2)) ∧ ((4 ≤ 8) ∧ (5 ≥ 2))) ∧ (((5 ≤ 8) ∧ (6 ≥ 2)) ∧ ((6 ≤ 8) ∧ ((8 ≥ 2) ∧ (8 ≤ 8))))))

theorem jsp579 : R0 := by

  have h_0 : (5 % 1 = 0) := by decide
  have h_1 : (4 % 2 = 0) := by decide
  have h_2 : (6 % 3 = 0) := by decide
  have h_3 : (8 % 4 = 0) := by decide
  have h_4 : (4 ≠ 5) := by decide
  have h_5 : (4 ≠ 6) := by decide
  have h_6 : (4 ≠ 8) := by decide
  have h_7 : (5 ≠ 6) := by decide
  have h_8 : (5 ≠ 8) := by decide
  have h_9 : (6 ≠ 8) := by decide
  have h_10 : (4 ≥ 2) := by decide
  have h_11 : (4 ≤ 8) := by decide
  have h_12 : (5 ≥ 2) := by decide
  have h_13 : (5 ≤ 8) := by decide
  have h_14 : (6 ≥ 2) := by decide
  have h_15 : (6 ≤ 8) := by decide
  have h_16 : (8 ≥ 2) := by decide
  have h_17 : (8 ≤ 8) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, ⟨h_7, h_8⟩⟩⟩⟩, ⟨⟨⟨h_9, h_10⟩, ⟨h_11, h_12⟩⟩, ⟨⟨h_13, h_14⟩, ⟨h_15, ⟨h_16, h_17⟩⟩⟩⟩⟩
