-- =====================================================================
-- JSP-000253 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can a subset of an integer interval be if no element's
--       reciprocal is a sum of reciprocals of other elements?
--
-- 构造：区间 [1,5] 的 5 元素全集 {1, 2, 3, 4, 5} 满足该性质：
--   对每个 a ∈ S 与其它元素的任意非空子集 T（不含 a），
--   用公共分母 M = lcm({a} ∪ T) 通分后验证 M / a ≠ Σ_{b∈T} M / b。
--   共 75 组检查，按 5 子句一组拆为 15 个引理，引理内逐子句 by
--   decide，主定理合取全部引理。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp253.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((2 / 1 ≠ 2 / 2) ∧ (3 / 1 ≠ 3 / 3)) ∧ ((4 / 1 ≠ 4 / 4) ∧ ((5 / 1 ≠ 5 / 5) ∧ (6 / 1 ≠ 6 / 2 + 6 / 3))))
theorem row0 : R0 := by
  have h_0 : (2 / 1 ≠ 2 / 2) := by decide
  have h_1 : (3 / 1 ≠ 3 / 3) := by decide
  have h_2 : (4 / 1 ≠ 4 / 4) := by decide
  have h_3 : (5 / 1 ≠ 5 / 5) := by decide
  have h_4 : (6 / 1 ≠ 6 / 2 + 6 / 3) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R1 : Prop := (((4 / 1 ≠ 4 / 2 + 4 / 4) ∧ (10 / 1 ≠ 10 / 2 + 10 / 5)) ∧ ((12 / 1 ≠ 12 / 3 + 12 / 4) ∧ ((15 / 1 ≠ 15 / 3 + 15 / 5) ∧ (20 / 1 ≠ 20 / 4 + 20 / 5))))
theorem row1 : R1 := by
  have h_0 : (4 / 1 ≠ 4 / 2 + 4 / 4) := by decide
  have h_1 : (10 / 1 ≠ 10 / 2 + 10 / 5) := by decide
  have h_2 : (12 / 1 ≠ 12 / 3 + 12 / 4) := by decide
  have h_3 : (15 / 1 ≠ 15 / 3 + 15 / 5) := by decide
  have h_4 : (20 / 1 ≠ 20 / 4 + 20 / 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R2 : Prop := (((12 / 1 ≠ 12 / 2 + 12 / 3 + 12 / 4) ∧ (30 / 1 ≠ 30 / 2 + 30 / 3 + 30 / 5)) ∧ ((20 / 1 ≠ 20 / 2 + 20 / 4 + 20 / 5) ∧ ((60 / 1 ≠ 60 / 3 + 60 / 4 + 60 / 5) ∧ (60 / 1 ≠ 60 / 2 + 60 / 3 + 60 / 4 + 60 / 5))))
theorem row2 : R2 := by
  have h_0 : (12 / 1 ≠ 12 / 2 + 12 / 3 + 12 / 4) := by decide
  have h_1 : (30 / 1 ≠ 30 / 2 + 30 / 3 + 30 / 5) := by decide
  have h_2 : (20 / 1 ≠ 20 / 2 + 20 / 4 + 20 / 5) := by decide
  have h_3 : (60 / 1 ≠ 60 / 3 + 60 / 4 + 60 / 5) := by decide
  have h_4 : (60 / 1 ≠ 60 / 2 + 60 / 3 + 60 / 4 + 60 / 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R3 : Prop := (((2 / 2 ≠ 2 / 1) ∧ (6 / 2 ≠ 6 / 3)) ∧ ((4 / 2 ≠ 4 / 4) ∧ ((10 / 2 ≠ 10 / 5) ∧ (6 / 2 ≠ 6 / 1 + 6 / 3))))
theorem row3 : R3 := by
  have h_0 : (2 / 2 ≠ 2 / 1) := by decide
  have h_1 : (6 / 2 ≠ 6 / 3) := by decide
  have h_2 : (4 / 2 ≠ 4 / 4) := by decide
  have h_3 : (10 / 2 ≠ 10 / 5) := by decide
  have h_4 : (6 / 2 ≠ 6 / 1 + 6 / 3) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R4 : Prop := (((4 / 2 ≠ 4 / 1 + 4 / 4) ∧ (10 / 2 ≠ 10 / 1 + 10 / 5)) ∧ ((12 / 2 ≠ 12 / 3 + 12 / 4) ∧ ((30 / 2 ≠ 30 / 3 + 30 / 5) ∧ (20 / 2 ≠ 20 / 4 + 20 / 5))))
theorem row4 : R4 := by
  have h_0 : (4 / 2 ≠ 4 / 1 + 4 / 4) := by decide
  have h_1 : (10 / 2 ≠ 10 / 1 + 10 / 5) := by decide
  have h_2 : (12 / 2 ≠ 12 / 3 + 12 / 4) := by decide
  have h_3 : (30 / 2 ≠ 30 / 3 + 30 / 5) := by decide
  have h_4 : (20 / 2 ≠ 20 / 4 + 20 / 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R5 : Prop := (((12 / 2 ≠ 12 / 1 + 12 / 3 + 12 / 4) ∧ (30 / 2 ≠ 30 / 1 + 30 / 3 + 30 / 5)) ∧ ((20 / 2 ≠ 20 / 1 + 20 / 4 + 20 / 5) ∧ ((60 / 2 ≠ 60 / 3 + 60 / 4 + 60 / 5) ∧ (60 / 2 ≠ 60 / 1 + 60 / 3 + 60 / 4 + 60 / 5))))
theorem row5 : R5 := by
  have h_0 : (12 / 2 ≠ 12 / 1 + 12 / 3 + 12 / 4) := by decide
  have h_1 : (30 / 2 ≠ 30 / 1 + 30 / 3 + 30 / 5) := by decide
  have h_2 : (20 / 2 ≠ 20 / 1 + 20 / 4 + 20 / 5) := by decide
  have h_3 : (60 / 2 ≠ 60 / 3 + 60 / 4 + 60 / 5) := by decide
  have h_4 : (60 / 2 ≠ 60 / 1 + 60 / 3 + 60 / 4 + 60 / 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R6 : Prop := (((3 / 3 ≠ 3 / 1) ∧ (6 / 3 ≠ 6 / 2)) ∧ ((12 / 3 ≠ 12 / 4) ∧ ((15 / 3 ≠ 15 / 5) ∧ (6 / 3 ≠ 6 / 1 + 6 / 2))))
theorem row6 : R6 := by
  have h_0 : (3 / 3 ≠ 3 / 1) := by decide
  have h_1 : (6 / 3 ≠ 6 / 2) := by decide
  have h_2 : (12 / 3 ≠ 12 / 4) := by decide
  have h_3 : (15 / 3 ≠ 15 / 5) := by decide
  have h_4 : (6 / 3 ≠ 6 / 1 + 6 / 2) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R7 : Prop := (((12 / 3 ≠ 12 / 1 + 12 / 4) ∧ (15 / 3 ≠ 15 / 1 + 15 / 5)) ∧ ((12 / 3 ≠ 12 / 2 + 12 / 4) ∧ ((30 / 3 ≠ 30 / 2 + 30 / 5) ∧ (60 / 3 ≠ 60 / 4 + 60 / 5))))
theorem row7 : R7 := by
  have h_0 : (12 / 3 ≠ 12 / 1 + 12 / 4) := by decide
  have h_1 : (15 / 3 ≠ 15 / 1 + 15 / 5) := by decide
  have h_2 : (12 / 3 ≠ 12 / 2 + 12 / 4) := by decide
  have h_3 : (30 / 3 ≠ 30 / 2 + 30 / 5) := by decide
  have h_4 : (60 / 3 ≠ 60 / 4 + 60 / 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R8 : Prop := (((12 / 3 ≠ 12 / 1 + 12 / 2 + 12 / 4) ∧ (30 / 3 ≠ 30 / 1 + 30 / 2 + 30 / 5)) ∧ ((60 / 3 ≠ 60 / 1 + 60 / 4 + 60 / 5) ∧ ((60 / 3 ≠ 60 / 2 + 60 / 4 + 60 / 5) ∧ (60 / 3 ≠ 60 / 1 + 60 / 2 + 60 / 4 + 60 / 5))))
theorem row8 : R8 := by
  have h_0 : (12 / 3 ≠ 12 / 1 + 12 / 2 + 12 / 4) := by decide
  have h_1 : (30 / 3 ≠ 30 / 1 + 30 / 2 + 30 / 5) := by decide
  have h_2 : (60 / 3 ≠ 60 / 1 + 60 / 4 + 60 / 5) := by decide
  have h_3 : (60 / 3 ≠ 60 / 2 + 60 / 4 + 60 / 5) := by decide
  have h_4 : (60 / 3 ≠ 60 / 1 + 60 / 2 + 60 / 4 + 60 / 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R9 : Prop := (((4 / 4 ≠ 4 / 1) ∧ (4 / 4 ≠ 4 / 2)) ∧ ((12 / 4 ≠ 12 / 3) ∧ ((20 / 4 ≠ 20 / 5) ∧ (4 / 4 ≠ 4 / 1 + 4 / 2))))
theorem row9 : R9 := by
  have h_0 : (4 / 4 ≠ 4 / 1) := by decide
  have h_1 : (4 / 4 ≠ 4 / 2) := by decide
  have h_2 : (12 / 4 ≠ 12 / 3) := by decide
  have h_3 : (20 / 4 ≠ 20 / 5) := by decide
  have h_4 : (4 / 4 ≠ 4 / 1 + 4 / 2) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R10 : Prop := (((12 / 4 ≠ 12 / 1 + 12 / 3) ∧ (20 / 4 ≠ 20 / 1 + 20 / 5)) ∧ ((12 / 4 ≠ 12 / 2 + 12 / 3) ∧ ((20 / 4 ≠ 20 / 2 + 20 / 5) ∧ (60 / 4 ≠ 60 / 3 + 60 / 5))))
theorem row10 : R10 := by
  have h_0 : (12 / 4 ≠ 12 / 1 + 12 / 3) := by decide
  have h_1 : (20 / 4 ≠ 20 / 1 + 20 / 5) := by decide
  have h_2 : (12 / 4 ≠ 12 / 2 + 12 / 3) := by decide
  have h_3 : (20 / 4 ≠ 20 / 2 + 20 / 5) := by decide
  have h_4 : (60 / 4 ≠ 60 / 3 + 60 / 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R11 : Prop := (((12 / 4 ≠ 12 / 1 + 12 / 2 + 12 / 3) ∧ (20 / 4 ≠ 20 / 1 + 20 / 2 + 20 / 5)) ∧ ((60 / 4 ≠ 60 / 1 + 60 / 3 + 60 / 5) ∧ ((60 / 4 ≠ 60 / 2 + 60 / 3 + 60 / 5) ∧ (60 / 4 ≠ 60 / 1 + 60 / 2 + 60 / 3 + 60 / 5))))
theorem row11 : R11 := by
  have h_0 : (12 / 4 ≠ 12 / 1 + 12 / 2 + 12 / 3) := by decide
  have h_1 : (20 / 4 ≠ 20 / 1 + 20 / 2 + 20 / 5) := by decide
  have h_2 : (60 / 4 ≠ 60 / 1 + 60 / 3 + 60 / 5) := by decide
  have h_3 : (60 / 4 ≠ 60 / 2 + 60 / 3 + 60 / 5) := by decide
  have h_4 : (60 / 4 ≠ 60 / 1 + 60 / 2 + 60 / 3 + 60 / 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R12 : Prop := (((5 / 5 ≠ 5 / 1) ∧ (10 / 5 ≠ 10 / 2)) ∧ ((15 / 5 ≠ 15 / 3) ∧ ((20 / 5 ≠ 20 / 4) ∧ (10 / 5 ≠ 10 / 1 + 10 / 2))))
theorem row12 : R12 := by
  have h_0 : (5 / 5 ≠ 5 / 1) := by decide
  have h_1 : (10 / 5 ≠ 10 / 2) := by decide
  have h_2 : (15 / 5 ≠ 15 / 3) := by decide
  have h_3 : (20 / 5 ≠ 20 / 4) := by decide
  have h_4 : (10 / 5 ≠ 10 / 1 + 10 / 2) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R13 : Prop := (((15 / 5 ≠ 15 / 1 + 15 / 3) ∧ (20 / 5 ≠ 20 / 1 + 20 / 4)) ∧ ((30 / 5 ≠ 30 / 2 + 30 / 3) ∧ ((20 / 5 ≠ 20 / 2 + 20 / 4) ∧ (60 / 5 ≠ 60 / 3 + 60 / 4))))
theorem row13 : R13 := by
  have h_0 : (15 / 5 ≠ 15 / 1 + 15 / 3) := by decide
  have h_1 : (20 / 5 ≠ 20 / 1 + 20 / 4) := by decide
  have h_2 : (30 / 5 ≠ 30 / 2 + 30 / 3) := by decide
  have h_3 : (20 / 5 ≠ 20 / 2 + 20 / 4) := by decide
  have h_4 : (60 / 5 ≠ 60 / 3 + 60 / 4) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R14 : Prop := (((30 / 5 ≠ 30 / 1 + 30 / 2 + 30 / 3) ∧ (20 / 5 ≠ 20 / 1 + 20 / 2 + 20 / 4)) ∧ ((60 / 5 ≠ 60 / 1 + 60 / 3 + 60 / 4) ∧ ((60 / 5 ≠ 60 / 2 + 60 / 3 + 60 / 4) ∧ (60 / 5 ≠ 60 / 1 + 60 / 2 + 60 / 3 + 60 / 4))))
theorem row14 : R14 := by
  have h_0 : (30 / 5 ≠ 30 / 1 + 30 / 2 + 30 / 3) := by decide
  have h_1 : (20 / 5 ≠ 20 / 1 + 20 / 2 + 20 / 4) := by decide
  have h_2 : (60 / 5 ≠ 60 / 1 + 60 / 3 + 60 / 4) := by decide
  have h_3 : (60 / 5 ≠ 60 / 2 + 60 / 3 + 60 / 4) := by decide
  have h_4 : (60 / 5 ≠ 60 / 1 + 60 / 2 + 60 / 3 + 60 / 4) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

theorem jsp253 :
  (((R0 ∧ (R1 ∧ R2)) ∧ ((R3 ∧ R4) ∧ (R5 ∧ R6))) ∧ (((R7 ∧ R8) ∧ (R9 ∧ R10)) ∧ ((R11 ∧ R12) ∧ (R13 ∧ R14)))) := by
  exact ⟨⟨⟨row0, ⟨row1, row2⟩⟩, ⟨⟨row3, row4⟩, ⟨row5, row6⟩⟩⟩, ⟨⟨⟨row7, row8⟩, ⟨row9, row10⟩⟩, ⟨⟨row11, row12⟩, ⟨row13, row14⟩⟩⟩⟩
