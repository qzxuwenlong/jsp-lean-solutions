-- =====================================================================
-- JSP-000430 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can an integer set be if it contains no three elements
--       with equal pairwise least common multiples?
--       （整数集合可多大，若其不含任何三元素，使三对两两最小公倍数
--       全相等？）
--
-- 构造：8 元素集合 {1, 2, 3, 4, 5, 7, 8, 9} ⊆ [1,30]。
--   对全部 C(8,3) = 56 个三元素子集 {a,b,c}，断言三对两两 lcm
--   不全相等：lcm(a,b) ≠ lcm(a,c) ∨ lcm(a,c) ≠ lcm(b,c)。
--   按 15 个一组拆为 4 个引理，引理内逐子句 by decide，主定理合取。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp430.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((Nat.lcm 1 2 ≠ Nat.lcm 1 3 ∨ Nat.lcm 1 3 ≠ Nat.lcm 2 3) ∧ ((Nat.lcm 1 2 ≠ Nat.lcm 1 4 ∨ Nat.lcm 1 4 ≠ Nat.lcm 2 4) ∧ (Nat.lcm 1 2 ≠ Nat.lcm 1 5 ∨ Nat.lcm 1 5 ≠ Nat.lcm 2 5))) ∧ (((Nat.lcm 1 2 ≠ Nat.lcm 1 7 ∨ Nat.lcm 1 7 ≠ Nat.lcm 2 7) ∧ (Nat.lcm 1 2 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 2 8)) ∧ ((Nat.lcm 1 2 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 2 9) ∧ (Nat.lcm 1 3 ≠ Nat.lcm 1 4 ∨ Nat.lcm 1 4 ≠ Nat.lcm 3 4)))) ∧ ((((Nat.lcm 1 3 ≠ Nat.lcm 1 5 ∨ Nat.lcm 1 5 ≠ Nat.lcm 3 5) ∧ (Nat.lcm 1 3 ≠ Nat.lcm 1 7 ∨ Nat.lcm 1 7 ≠ Nat.lcm 3 7)) ∧ ((Nat.lcm 1 3 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 3 8) ∧ (Nat.lcm 1 3 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 3 9))) ∧ (((Nat.lcm 1 4 ≠ Nat.lcm 1 5 ∨ Nat.lcm 1 5 ≠ Nat.lcm 4 5) ∧ (Nat.lcm 1 4 ≠ Nat.lcm 1 7 ∨ Nat.lcm 1 7 ≠ Nat.lcm 4 7)) ∧ ((Nat.lcm 1 4 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 4 8) ∧ (Nat.lcm 1 4 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 4 9)))))
theorem row0 : R0 := by
  have h_0 : (Nat.lcm 1 2 ≠ Nat.lcm 1 3 ∨ Nat.lcm 1 3 ≠ Nat.lcm 2 3) := by decide
  have h_1 : (Nat.lcm 1 2 ≠ Nat.lcm 1 4 ∨ Nat.lcm 1 4 ≠ Nat.lcm 2 4) := by decide
  have h_2 : (Nat.lcm 1 2 ≠ Nat.lcm 1 5 ∨ Nat.lcm 1 5 ≠ Nat.lcm 2 5) := by decide
  have h_3 : (Nat.lcm 1 2 ≠ Nat.lcm 1 7 ∨ Nat.lcm 1 7 ≠ Nat.lcm 2 7) := by decide
  have h_4 : (Nat.lcm 1 2 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 2 8) := by decide
  have h_5 : (Nat.lcm 1 2 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 2 9) := by decide
  have h_6 : (Nat.lcm 1 3 ≠ Nat.lcm 1 4 ∨ Nat.lcm 1 4 ≠ Nat.lcm 3 4) := by decide
  have h_7 : (Nat.lcm 1 3 ≠ Nat.lcm 1 5 ∨ Nat.lcm 1 5 ≠ Nat.lcm 3 5) := by decide
  have h_8 : (Nat.lcm 1 3 ≠ Nat.lcm 1 7 ∨ Nat.lcm 1 7 ≠ Nat.lcm 3 7) := by decide
  have h_9 : (Nat.lcm 1 3 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 3 8) := by decide
  have h_10 : (Nat.lcm 1 3 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 3 9) := by decide
  have h_11 : (Nat.lcm 1 4 ≠ Nat.lcm 1 5 ∨ Nat.lcm 1 5 ≠ Nat.lcm 4 5) := by decide
  have h_12 : (Nat.lcm 1 4 ≠ Nat.lcm 1 7 ∨ Nat.lcm 1 7 ≠ Nat.lcm 4 7) := by decide
  have h_13 : (Nat.lcm 1 4 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 4 8) := by decide
  have h_14 : (Nat.lcm 1 4 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 4 9) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R1 : Prop := ((((Nat.lcm 1 5 ≠ Nat.lcm 1 7 ∨ Nat.lcm 1 7 ≠ Nat.lcm 5 7) ∧ ((Nat.lcm 1 5 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 5 8) ∧ (Nat.lcm 1 5 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 5 9))) ∧ (((Nat.lcm 1 7 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 7 8) ∧ (Nat.lcm 1 7 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 7 9)) ∧ ((Nat.lcm 1 8 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 8 9) ∧ (Nat.lcm 2 3 ≠ Nat.lcm 2 4 ∨ Nat.lcm 2 4 ≠ Nat.lcm 3 4)))) ∧ ((((Nat.lcm 2 3 ≠ Nat.lcm 2 5 ∨ Nat.lcm 2 5 ≠ Nat.lcm 3 5) ∧ (Nat.lcm 2 3 ≠ Nat.lcm 2 7 ∨ Nat.lcm 2 7 ≠ Nat.lcm 3 7)) ∧ ((Nat.lcm 2 3 ≠ Nat.lcm 2 8 ∨ Nat.lcm 2 8 ≠ Nat.lcm 3 8) ∧ (Nat.lcm 2 3 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 3 9))) ∧ (((Nat.lcm 2 4 ≠ Nat.lcm 2 5 ∨ Nat.lcm 2 5 ≠ Nat.lcm 4 5) ∧ (Nat.lcm 2 4 ≠ Nat.lcm 2 7 ∨ Nat.lcm 2 7 ≠ Nat.lcm 4 7)) ∧ ((Nat.lcm 2 4 ≠ Nat.lcm 2 8 ∨ Nat.lcm 2 8 ≠ Nat.lcm 4 8) ∧ (Nat.lcm 2 4 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 4 9)))))
theorem row1 : R1 := by
  have h_0 : (Nat.lcm 1 5 ≠ Nat.lcm 1 7 ∨ Nat.lcm 1 7 ≠ Nat.lcm 5 7) := by decide
  have h_1 : (Nat.lcm 1 5 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 5 8) := by decide
  have h_2 : (Nat.lcm 1 5 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 5 9) := by decide
  have h_3 : (Nat.lcm 1 7 ≠ Nat.lcm 1 8 ∨ Nat.lcm 1 8 ≠ Nat.lcm 7 8) := by decide
  have h_4 : (Nat.lcm 1 7 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 7 9) := by decide
  have h_5 : (Nat.lcm 1 8 ≠ Nat.lcm 1 9 ∨ Nat.lcm 1 9 ≠ Nat.lcm 8 9) := by decide
  have h_6 : (Nat.lcm 2 3 ≠ Nat.lcm 2 4 ∨ Nat.lcm 2 4 ≠ Nat.lcm 3 4) := by decide
  have h_7 : (Nat.lcm 2 3 ≠ Nat.lcm 2 5 ∨ Nat.lcm 2 5 ≠ Nat.lcm 3 5) := by decide
  have h_8 : (Nat.lcm 2 3 ≠ Nat.lcm 2 7 ∨ Nat.lcm 2 7 ≠ Nat.lcm 3 7) := by decide
  have h_9 : (Nat.lcm 2 3 ≠ Nat.lcm 2 8 ∨ Nat.lcm 2 8 ≠ Nat.lcm 3 8) := by decide
  have h_10 : (Nat.lcm 2 3 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 3 9) := by decide
  have h_11 : (Nat.lcm 2 4 ≠ Nat.lcm 2 5 ∨ Nat.lcm 2 5 ≠ Nat.lcm 4 5) := by decide
  have h_12 : (Nat.lcm 2 4 ≠ Nat.lcm 2 7 ∨ Nat.lcm 2 7 ≠ Nat.lcm 4 7) := by decide
  have h_13 : (Nat.lcm 2 4 ≠ Nat.lcm 2 8 ∨ Nat.lcm 2 8 ≠ Nat.lcm 4 8) := by decide
  have h_14 : (Nat.lcm 2 4 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 4 9) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R2 : Prop := ((((Nat.lcm 2 5 ≠ Nat.lcm 2 7 ∨ Nat.lcm 2 7 ≠ Nat.lcm 5 7) ∧ ((Nat.lcm 2 5 ≠ Nat.lcm 2 8 ∨ Nat.lcm 2 8 ≠ Nat.lcm 5 8) ∧ (Nat.lcm 2 5 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 5 9))) ∧ (((Nat.lcm 2 7 ≠ Nat.lcm 2 8 ∨ Nat.lcm 2 8 ≠ Nat.lcm 7 8) ∧ (Nat.lcm 2 7 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 7 9)) ∧ ((Nat.lcm 2 8 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 8 9) ∧ (Nat.lcm 3 4 ≠ Nat.lcm 3 5 ∨ Nat.lcm 3 5 ≠ Nat.lcm 4 5)))) ∧ ((((Nat.lcm 3 4 ≠ Nat.lcm 3 7 ∨ Nat.lcm 3 7 ≠ Nat.lcm 4 7) ∧ (Nat.lcm 3 4 ≠ Nat.lcm 3 8 ∨ Nat.lcm 3 8 ≠ Nat.lcm 4 8)) ∧ ((Nat.lcm 3 4 ≠ Nat.lcm 3 9 ∨ Nat.lcm 3 9 ≠ Nat.lcm 4 9) ∧ (Nat.lcm 3 5 ≠ Nat.lcm 3 7 ∨ Nat.lcm 3 7 ≠ Nat.lcm 5 7))) ∧ (((Nat.lcm 3 5 ≠ Nat.lcm 3 8 ∨ Nat.lcm 3 8 ≠ Nat.lcm 5 8) ∧ (Nat.lcm 3 5 ≠ Nat.lcm 3 9 ∨ Nat.lcm 3 9 ≠ Nat.lcm 5 9)) ∧ ((Nat.lcm 3 7 ≠ Nat.lcm 3 8 ∨ Nat.lcm 3 8 ≠ Nat.lcm 7 8) ∧ (Nat.lcm 3 7 ≠ Nat.lcm 3 9 ∨ Nat.lcm 3 9 ≠ Nat.lcm 7 9)))))
theorem row2 : R2 := by
  have h_0 : (Nat.lcm 2 5 ≠ Nat.lcm 2 7 ∨ Nat.lcm 2 7 ≠ Nat.lcm 5 7) := by decide
  have h_1 : (Nat.lcm 2 5 ≠ Nat.lcm 2 8 ∨ Nat.lcm 2 8 ≠ Nat.lcm 5 8) := by decide
  have h_2 : (Nat.lcm 2 5 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 5 9) := by decide
  have h_3 : (Nat.lcm 2 7 ≠ Nat.lcm 2 8 ∨ Nat.lcm 2 8 ≠ Nat.lcm 7 8) := by decide
  have h_4 : (Nat.lcm 2 7 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 7 9) := by decide
  have h_5 : (Nat.lcm 2 8 ≠ Nat.lcm 2 9 ∨ Nat.lcm 2 9 ≠ Nat.lcm 8 9) := by decide
  have h_6 : (Nat.lcm 3 4 ≠ Nat.lcm 3 5 ∨ Nat.lcm 3 5 ≠ Nat.lcm 4 5) := by decide
  have h_7 : (Nat.lcm 3 4 ≠ Nat.lcm 3 7 ∨ Nat.lcm 3 7 ≠ Nat.lcm 4 7) := by decide
  have h_8 : (Nat.lcm 3 4 ≠ Nat.lcm 3 8 ∨ Nat.lcm 3 8 ≠ Nat.lcm 4 8) := by decide
  have h_9 : (Nat.lcm 3 4 ≠ Nat.lcm 3 9 ∨ Nat.lcm 3 9 ≠ Nat.lcm 4 9) := by decide
  have h_10 : (Nat.lcm 3 5 ≠ Nat.lcm 3 7 ∨ Nat.lcm 3 7 ≠ Nat.lcm 5 7) := by decide
  have h_11 : (Nat.lcm 3 5 ≠ Nat.lcm 3 8 ∨ Nat.lcm 3 8 ≠ Nat.lcm 5 8) := by decide
  have h_12 : (Nat.lcm 3 5 ≠ Nat.lcm 3 9 ∨ Nat.lcm 3 9 ≠ Nat.lcm 5 9) := by decide
  have h_13 : (Nat.lcm 3 7 ≠ Nat.lcm 3 8 ∨ Nat.lcm 3 8 ≠ Nat.lcm 7 8) := by decide
  have h_14 : (Nat.lcm 3 7 ≠ Nat.lcm 3 9 ∨ Nat.lcm 3 9 ≠ Nat.lcm 7 9) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R3 : Prop := ((((Nat.lcm 3 8 ≠ Nat.lcm 3 9 ∨ Nat.lcm 3 9 ≠ Nat.lcm 8 9) ∧ (Nat.lcm 4 5 ≠ Nat.lcm 4 7 ∨ Nat.lcm 4 7 ≠ Nat.lcm 5 7)) ∧ ((Nat.lcm 4 5 ≠ Nat.lcm 4 8 ∨ Nat.lcm 4 8 ≠ Nat.lcm 5 8) ∧ ((Nat.lcm 4 5 ≠ Nat.lcm 4 9 ∨ Nat.lcm 4 9 ≠ Nat.lcm 5 9) ∧ (Nat.lcm 4 7 ≠ Nat.lcm 4 8 ∨ Nat.lcm 4 8 ≠ Nat.lcm 7 8)))) ∧ (((Nat.lcm 4 7 ≠ Nat.lcm 4 9 ∨ Nat.lcm 4 9 ≠ Nat.lcm 7 9) ∧ ((Nat.lcm 4 8 ≠ Nat.lcm 4 9 ∨ Nat.lcm 4 9 ≠ Nat.lcm 8 9) ∧ (Nat.lcm 5 7 ≠ Nat.lcm 5 8 ∨ Nat.lcm 5 8 ≠ Nat.lcm 7 8))) ∧ ((Nat.lcm 5 7 ≠ Nat.lcm 5 9 ∨ Nat.lcm 5 9 ≠ Nat.lcm 7 9) ∧ ((Nat.lcm 5 8 ≠ Nat.lcm 5 9 ∨ Nat.lcm 5 9 ≠ Nat.lcm 8 9) ∧ (Nat.lcm 7 8 ≠ Nat.lcm 7 9 ∨ Nat.lcm 7 9 ≠ Nat.lcm 8 9)))))
theorem row3 : R3 := by
  have h_0 : (Nat.lcm 3 8 ≠ Nat.lcm 3 9 ∨ Nat.lcm 3 9 ≠ Nat.lcm 8 9) := by decide
  have h_1 : (Nat.lcm 4 5 ≠ Nat.lcm 4 7 ∨ Nat.lcm 4 7 ≠ Nat.lcm 5 7) := by decide
  have h_2 : (Nat.lcm 4 5 ≠ Nat.lcm 4 8 ∨ Nat.lcm 4 8 ≠ Nat.lcm 5 8) := by decide
  have h_3 : (Nat.lcm 4 5 ≠ Nat.lcm 4 9 ∨ Nat.lcm 4 9 ≠ Nat.lcm 5 9) := by decide
  have h_4 : (Nat.lcm 4 7 ≠ Nat.lcm 4 8 ∨ Nat.lcm 4 8 ≠ Nat.lcm 7 8) := by decide
  have h_5 : (Nat.lcm 4 7 ≠ Nat.lcm 4 9 ∨ Nat.lcm 4 9 ≠ Nat.lcm 7 9) := by decide
  have h_6 : (Nat.lcm 4 8 ≠ Nat.lcm 4 9 ∨ Nat.lcm 4 9 ≠ Nat.lcm 8 9) := by decide
  have h_7 : (Nat.lcm 5 7 ≠ Nat.lcm 5 8 ∨ Nat.lcm 5 8 ≠ Nat.lcm 7 8) := by decide
  have h_8 : (Nat.lcm 5 7 ≠ Nat.lcm 5 9 ∨ Nat.lcm 5 9 ≠ Nat.lcm 7 9) := by decide
  have h_9 : (Nat.lcm 5 8 ≠ Nat.lcm 5 9 ∨ Nat.lcm 5 9 ≠ Nat.lcm 8 9) := by decide
  have h_10 : (Nat.lcm 7 8 ≠ Nat.lcm 7 9 ∨ Nat.lcm 7 9 ≠ Nat.lcm 8 9) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, ⟨h_6, h_7⟩⟩, ⟨h_8, ⟨h_9, h_10⟩⟩⟩⟩

theorem jsp430 :
  ((R0 ∧ R1) ∧ (R2 ∧ R3)) := by
  exact ⟨⟨row0, row1⟩, ⟨row2, row3⟩⟩
