-- =====================================================================
-- JSP-000429 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can an integer set be if it contains no prescribed-size
--       subset with all pairwise greatest common divisors equal?
--       （整数集合可多大，若其不含任何固定大小子集，使所有两两最大
--       公约数全相等？）
--
-- 构造：8 元素集合 {4, 8, 9, 10, 15, 16, 27, 30} ⊆ [1,30]。
--   对全部 C(8,3) = 56 个三元素子集 {a,b,c}，断言三对两两 gcd
--   不全相等：gcd(a,b) ≠ gcd(a,c) ∨ gcd(a,c) ≠ gcd(b,c)。
--   按 15 个一组拆为 4 个引理，引理内逐子句 by decide，主定理合取。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp429.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((Nat.gcd 4 8 ≠ Nat.gcd 4 9 ∨ Nat.gcd 4 9 ≠ Nat.gcd 8 9) ∧ ((Nat.gcd 4 8 ≠ Nat.gcd 4 10 ∨ Nat.gcd 4 10 ≠ Nat.gcd 8 10) ∧ (Nat.gcd 4 8 ≠ Nat.gcd 4 15 ∨ Nat.gcd 4 15 ≠ Nat.gcd 8 15))) ∧ (((Nat.gcd 4 8 ≠ Nat.gcd 4 16 ∨ Nat.gcd 4 16 ≠ Nat.gcd 8 16) ∧ (Nat.gcd 4 8 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 8 27)) ∧ ((Nat.gcd 4 8 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 8 30) ∧ (Nat.gcd 4 9 ≠ Nat.gcd 4 10 ∨ Nat.gcd 4 10 ≠ Nat.gcd 9 10)))) ∧ ((((Nat.gcd 4 9 ≠ Nat.gcd 4 15 ∨ Nat.gcd 4 15 ≠ Nat.gcd 9 15) ∧ (Nat.gcd 4 9 ≠ Nat.gcd 4 16 ∨ Nat.gcd 4 16 ≠ Nat.gcd 9 16)) ∧ ((Nat.gcd 4 9 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 9 27) ∧ (Nat.gcd 4 9 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 9 30))) ∧ (((Nat.gcd 4 10 ≠ Nat.gcd 4 15 ∨ Nat.gcd 4 15 ≠ Nat.gcd 10 15) ∧ (Nat.gcd 4 10 ≠ Nat.gcd 4 16 ∨ Nat.gcd 4 16 ≠ Nat.gcd 10 16)) ∧ ((Nat.gcd 4 10 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 10 27) ∧ (Nat.gcd 4 10 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 10 30)))))
theorem row0 : R0 := by
  have h_0 : (Nat.gcd 4 8 ≠ Nat.gcd 4 9 ∨ Nat.gcd 4 9 ≠ Nat.gcd 8 9) := by decide
  have h_1 : (Nat.gcd 4 8 ≠ Nat.gcd 4 10 ∨ Nat.gcd 4 10 ≠ Nat.gcd 8 10) := by decide
  have h_2 : (Nat.gcd 4 8 ≠ Nat.gcd 4 15 ∨ Nat.gcd 4 15 ≠ Nat.gcd 8 15) := by decide
  have h_3 : (Nat.gcd 4 8 ≠ Nat.gcd 4 16 ∨ Nat.gcd 4 16 ≠ Nat.gcd 8 16) := by decide
  have h_4 : (Nat.gcd 4 8 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 8 27) := by decide
  have h_5 : (Nat.gcd 4 8 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 8 30) := by decide
  have h_6 : (Nat.gcd 4 9 ≠ Nat.gcd 4 10 ∨ Nat.gcd 4 10 ≠ Nat.gcd 9 10) := by decide
  have h_7 : (Nat.gcd 4 9 ≠ Nat.gcd 4 15 ∨ Nat.gcd 4 15 ≠ Nat.gcd 9 15) := by decide
  have h_8 : (Nat.gcd 4 9 ≠ Nat.gcd 4 16 ∨ Nat.gcd 4 16 ≠ Nat.gcd 9 16) := by decide
  have h_9 : (Nat.gcd 4 9 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 9 27) := by decide
  have h_10 : (Nat.gcd 4 9 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 9 30) := by decide
  have h_11 : (Nat.gcd 4 10 ≠ Nat.gcd 4 15 ∨ Nat.gcd 4 15 ≠ Nat.gcd 10 15) := by decide
  have h_12 : (Nat.gcd 4 10 ≠ Nat.gcd 4 16 ∨ Nat.gcd 4 16 ≠ Nat.gcd 10 16) := by decide
  have h_13 : (Nat.gcd 4 10 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 10 27) := by decide
  have h_14 : (Nat.gcd 4 10 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 10 30) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R1 : Prop := ((((Nat.gcd 4 15 ≠ Nat.gcd 4 16 ∨ Nat.gcd 4 16 ≠ Nat.gcd 15 16) ∧ ((Nat.gcd 4 15 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 15 27) ∧ (Nat.gcd 4 15 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 15 30))) ∧ (((Nat.gcd 4 16 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 16 27) ∧ (Nat.gcd 4 16 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 16 30)) ∧ ((Nat.gcd 4 27 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 27 30) ∧ (Nat.gcd 8 9 ≠ Nat.gcd 8 10 ∨ Nat.gcd 8 10 ≠ Nat.gcd 9 10)))) ∧ ((((Nat.gcd 8 9 ≠ Nat.gcd 8 15 ∨ Nat.gcd 8 15 ≠ Nat.gcd 9 15) ∧ (Nat.gcd 8 9 ≠ Nat.gcd 8 16 ∨ Nat.gcd 8 16 ≠ Nat.gcd 9 16)) ∧ ((Nat.gcd 8 9 ≠ Nat.gcd 8 27 ∨ Nat.gcd 8 27 ≠ Nat.gcd 9 27) ∧ (Nat.gcd 8 9 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 9 30))) ∧ (((Nat.gcd 8 10 ≠ Nat.gcd 8 15 ∨ Nat.gcd 8 15 ≠ Nat.gcd 10 15) ∧ (Nat.gcd 8 10 ≠ Nat.gcd 8 16 ∨ Nat.gcd 8 16 ≠ Nat.gcd 10 16)) ∧ ((Nat.gcd 8 10 ≠ Nat.gcd 8 27 ∨ Nat.gcd 8 27 ≠ Nat.gcd 10 27) ∧ (Nat.gcd 8 10 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 10 30)))))
theorem row1 : R1 := by
  have h_0 : (Nat.gcd 4 15 ≠ Nat.gcd 4 16 ∨ Nat.gcd 4 16 ≠ Nat.gcd 15 16) := by decide
  have h_1 : (Nat.gcd 4 15 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 15 27) := by decide
  have h_2 : (Nat.gcd 4 15 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 15 30) := by decide
  have h_3 : (Nat.gcd 4 16 ≠ Nat.gcd 4 27 ∨ Nat.gcd 4 27 ≠ Nat.gcd 16 27) := by decide
  have h_4 : (Nat.gcd 4 16 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 16 30) := by decide
  have h_5 : (Nat.gcd 4 27 ≠ Nat.gcd 4 30 ∨ Nat.gcd 4 30 ≠ Nat.gcd 27 30) := by decide
  have h_6 : (Nat.gcd 8 9 ≠ Nat.gcd 8 10 ∨ Nat.gcd 8 10 ≠ Nat.gcd 9 10) := by decide
  have h_7 : (Nat.gcd 8 9 ≠ Nat.gcd 8 15 ∨ Nat.gcd 8 15 ≠ Nat.gcd 9 15) := by decide
  have h_8 : (Nat.gcd 8 9 ≠ Nat.gcd 8 16 ∨ Nat.gcd 8 16 ≠ Nat.gcd 9 16) := by decide
  have h_9 : (Nat.gcd 8 9 ≠ Nat.gcd 8 27 ∨ Nat.gcd 8 27 ≠ Nat.gcd 9 27) := by decide
  have h_10 : (Nat.gcd 8 9 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 9 30) := by decide
  have h_11 : (Nat.gcd 8 10 ≠ Nat.gcd 8 15 ∨ Nat.gcd 8 15 ≠ Nat.gcd 10 15) := by decide
  have h_12 : (Nat.gcd 8 10 ≠ Nat.gcd 8 16 ∨ Nat.gcd 8 16 ≠ Nat.gcd 10 16) := by decide
  have h_13 : (Nat.gcd 8 10 ≠ Nat.gcd 8 27 ∨ Nat.gcd 8 27 ≠ Nat.gcd 10 27) := by decide
  have h_14 : (Nat.gcd 8 10 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 10 30) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R2 : Prop := ((((Nat.gcd 8 15 ≠ Nat.gcd 8 16 ∨ Nat.gcd 8 16 ≠ Nat.gcd 15 16) ∧ ((Nat.gcd 8 15 ≠ Nat.gcd 8 27 ∨ Nat.gcd 8 27 ≠ Nat.gcd 15 27) ∧ (Nat.gcd 8 15 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 15 30))) ∧ (((Nat.gcd 8 16 ≠ Nat.gcd 8 27 ∨ Nat.gcd 8 27 ≠ Nat.gcd 16 27) ∧ (Nat.gcd 8 16 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 16 30)) ∧ ((Nat.gcd 8 27 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 27 30) ∧ (Nat.gcd 9 10 ≠ Nat.gcd 9 15 ∨ Nat.gcd 9 15 ≠ Nat.gcd 10 15)))) ∧ ((((Nat.gcd 9 10 ≠ Nat.gcd 9 16 ∨ Nat.gcd 9 16 ≠ Nat.gcd 10 16) ∧ (Nat.gcd 9 10 ≠ Nat.gcd 9 27 ∨ Nat.gcd 9 27 ≠ Nat.gcd 10 27)) ∧ ((Nat.gcd 9 10 ≠ Nat.gcd 9 30 ∨ Nat.gcd 9 30 ≠ Nat.gcd 10 30) ∧ (Nat.gcd 9 15 ≠ Nat.gcd 9 16 ∨ Nat.gcd 9 16 ≠ Nat.gcd 15 16))) ∧ (((Nat.gcd 9 15 ≠ Nat.gcd 9 27 ∨ Nat.gcd 9 27 ≠ Nat.gcd 15 27) ∧ (Nat.gcd 9 15 ≠ Nat.gcd 9 30 ∨ Nat.gcd 9 30 ≠ Nat.gcd 15 30)) ∧ ((Nat.gcd 9 16 ≠ Nat.gcd 9 27 ∨ Nat.gcd 9 27 ≠ Nat.gcd 16 27) ∧ (Nat.gcd 9 16 ≠ Nat.gcd 9 30 ∨ Nat.gcd 9 30 ≠ Nat.gcd 16 30)))))
theorem row2 : R2 := by
  have h_0 : (Nat.gcd 8 15 ≠ Nat.gcd 8 16 ∨ Nat.gcd 8 16 ≠ Nat.gcd 15 16) := by decide
  have h_1 : (Nat.gcd 8 15 ≠ Nat.gcd 8 27 ∨ Nat.gcd 8 27 ≠ Nat.gcd 15 27) := by decide
  have h_2 : (Nat.gcd 8 15 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 15 30) := by decide
  have h_3 : (Nat.gcd 8 16 ≠ Nat.gcd 8 27 ∨ Nat.gcd 8 27 ≠ Nat.gcd 16 27) := by decide
  have h_4 : (Nat.gcd 8 16 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 16 30) := by decide
  have h_5 : (Nat.gcd 8 27 ≠ Nat.gcd 8 30 ∨ Nat.gcd 8 30 ≠ Nat.gcd 27 30) := by decide
  have h_6 : (Nat.gcd 9 10 ≠ Nat.gcd 9 15 ∨ Nat.gcd 9 15 ≠ Nat.gcd 10 15) := by decide
  have h_7 : (Nat.gcd 9 10 ≠ Nat.gcd 9 16 ∨ Nat.gcd 9 16 ≠ Nat.gcd 10 16) := by decide
  have h_8 : (Nat.gcd 9 10 ≠ Nat.gcd 9 27 ∨ Nat.gcd 9 27 ≠ Nat.gcd 10 27) := by decide
  have h_9 : (Nat.gcd 9 10 ≠ Nat.gcd 9 30 ∨ Nat.gcd 9 30 ≠ Nat.gcd 10 30) := by decide
  have h_10 : (Nat.gcd 9 15 ≠ Nat.gcd 9 16 ∨ Nat.gcd 9 16 ≠ Nat.gcd 15 16) := by decide
  have h_11 : (Nat.gcd 9 15 ≠ Nat.gcd 9 27 ∨ Nat.gcd 9 27 ≠ Nat.gcd 15 27) := by decide
  have h_12 : (Nat.gcd 9 15 ≠ Nat.gcd 9 30 ∨ Nat.gcd 9 30 ≠ Nat.gcd 15 30) := by decide
  have h_13 : (Nat.gcd 9 16 ≠ Nat.gcd 9 27 ∨ Nat.gcd 9 27 ≠ Nat.gcd 16 27) := by decide
  have h_14 : (Nat.gcd 9 16 ≠ Nat.gcd 9 30 ∨ Nat.gcd 9 30 ≠ Nat.gcd 16 30) := by decide
  exact ⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨⟨h_7, h_8⟩, ⟨h_9, h_10⟩⟩, ⟨⟨h_11, h_12⟩, ⟨h_13, h_14⟩⟩⟩⟩

def R3 : Prop := ((((Nat.gcd 9 27 ≠ Nat.gcd 9 30 ∨ Nat.gcd 9 30 ≠ Nat.gcd 27 30) ∧ (Nat.gcd 10 15 ≠ Nat.gcd 10 16 ∨ Nat.gcd 10 16 ≠ Nat.gcd 15 16)) ∧ ((Nat.gcd 10 15 ≠ Nat.gcd 10 27 ∨ Nat.gcd 10 27 ≠ Nat.gcd 15 27) ∧ ((Nat.gcd 10 15 ≠ Nat.gcd 10 30 ∨ Nat.gcd 10 30 ≠ Nat.gcd 15 30) ∧ (Nat.gcd 10 16 ≠ Nat.gcd 10 27 ∨ Nat.gcd 10 27 ≠ Nat.gcd 16 27)))) ∧ (((Nat.gcd 10 16 ≠ Nat.gcd 10 30 ∨ Nat.gcd 10 30 ≠ Nat.gcd 16 30) ∧ ((Nat.gcd 10 27 ≠ Nat.gcd 10 30 ∨ Nat.gcd 10 30 ≠ Nat.gcd 27 30) ∧ (Nat.gcd 15 16 ≠ Nat.gcd 15 27 ∨ Nat.gcd 15 27 ≠ Nat.gcd 16 27))) ∧ ((Nat.gcd 15 16 ≠ Nat.gcd 15 30 ∨ Nat.gcd 15 30 ≠ Nat.gcd 16 30) ∧ ((Nat.gcd 15 27 ≠ Nat.gcd 15 30 ∨ Nat.gcd 15 30 ≠ Nat.gcd 27 30) ∧ (Nat.gcd 16 27 ≠ Nat.gcd 16 30 ∨ Nat.gcd 16 30 ≠ Nat.gcd 27 30)))))
theorem row3 : R3 := by
  have h_0 : (Nat.gcd 9 27 ≠ Nat.gcd 9 30 ∨ Nat.gcd 9 30 ≠ Nat.gcd 27 30) := by decide
  have h_1 : (Nat.gcd 10 15 ≠ Nat.gcd 10 16 ∨ Nat.gcd 10 16 ≠ Nat.gcd 15 16) := by decide
  have h_2 : (Nat.gcd 10 15 ≠ Nat.gcd 10 27 ∨ Nat.gcd 10 27 ≠ Nat.gcd 15 27) := by decide
  have h_3 : (Nat.gcd 10 15 ≠ Nat.gcd 10 30 ∨ Nat.gcd 10 30 ≠ Nat.gcd 15 30) := by decide
  have h_4 : (Nat.gcd 10 16 ≠ Nat.gcd 10 27 ∨ Nat.gcd 10 27 ≠ Nat.gcd 16 27) := by decide
  have h_5 : (Nat.gcd 10 16 ≠ Nat.gcd 10 30 ∨ Nat.gcd 10 30 ≠ Nat.gcd 16 30) := by decide
  have h_6 : (Nat.gcd 10 27 ≠ Nat.gcd 10 30 ∨ Nat.gcd 10 30 ≠ Nat.gcd 27 30) := by decide
  have h_7 : (Nat.gcd 15 16 ≠ Nat.gcd 15 27 ∨ Nat.gcd 15 27 ≠ Nat.gcd 16 27) := by decide
  have h_8 : (Nat.gcd 15 16 ≠ Nat.gcd 15 30 ∨ Nat.gcd 15 30 ≠ Nat.gcd 16 30) := by decide
  have h_9 : (Nat.gcd 15 27 ≠ Nat.gcd 15 30 ∨ Nat.gcd 15 30 ≠ Nat.gcd 27 30) := by decide
  have h_10 : (Nat.gcd 16 27 ≠ Nat.gcd 16 30 ∨ Nat.gcd 16 30 ≠ Nat.gcd 27 30) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, ⟨h_6, h_7⟩⟩, ⟨h_8, ⟨h_9, h_10⟩⟩⟩⟩

theorem jsp429 :
  ((R0 ∧ R1) ∧ (R2 ∧ R3)) := by
  exact ⟨⟨row0, row1⟩, ⟨row2, row3⟩⟩
