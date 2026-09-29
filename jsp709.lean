-- =====================================================================
-- JSP-000709 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can an integer set's reciprocal sum be if it has no
--       prescribed-size subset with all pairwise least common multiples
--       equal?
--       （若整数集不含"两两最小公倍数全相等"的指定大小子集，其
--       倒数和可以多大？）
--
-- 构造：7 元素子集 A = {1, 2, 3, 4, 5, 7, 8} ⊆ [1, 8]：
--   · 任意三元素 {a,b,c} ⊆ A：lcm(a,b)、lcm(a,c)、lcm(b,c) 不全相等
--     （35 个三元组，每行 5 个共 7 行，全部闭项验证）；
--   · 倒数总和 Σ_{d∈A} 1/d = 2143/840：
--     lcm(1..8) = 840，分子 840/d 依次为
--     840, 420, 280, 210, 168, 120, 105，分子和 = 2143；
--   · gcd(2143, 840) = 1（最简分数）。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp709.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((¬(Nat.lcm 1 2 = Nat.lcm 1 3 ∧ Nat.lcm 1 3 = Nat.lcm 2 3) ∧ ¬(Nat.lcm 1 2 = Nat.lcm 1 4 ∧ Nat.lcm 1 4 = Nat.lcm 2 4)) ∧ (¬(Nat.lcm 1 2 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 2 5) ∧ (¬(Nat.lcm 1 2 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 2 7) ∧ ¬(Nat.lcm 1 2 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 2 8))))
theorem row0 : R0 := by
  have h_0 : ¬(Nat.lcm 1 2 = Nat.lcm 1 3 ∧ Nat.lcm 1 3 = Nat.lcm 2 3) := by decide
  have h_1 : ¬(Nat.lcm 1 2 = Nat.lcm 1 4 ∧ Nat.lcm 1 4 = Nat.lcm 2 4) := by decide
  have h_2 : ¬(Nat.lcm 1 2 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 2 5) := by decide
  have h_3 : ¬(Nat.lcm 1 2 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 2 7) := by decide
  have h_4 : ¬(Nat.lcm 1 2 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 2 8) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R1 : Prop := ((¬(Nat.lcm 1 3 = Nat.lcm 1 4 ∧ Nat.lcm 1 4 = Nat.lcm 3 4) ∧ ¬(Nat.lcm 1 3 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 3 5)) ∧ (¬(Nat.lcm 1 3 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 3 7) ∧ (¬(Nat.lcm 1 3 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 3 8) ∧ ¬(Nat.lcm 1 4 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 4 5))))
theorem row1 : R1 := by
  have h_0 : ¬(Nat.lcm 1 3 = Nat.lcm 1 4 ∧ Nat.lcm 1 4 = Nat.lcm 3 4) := by decide
  have h_1 : ¬(Nat.lcm 1 3 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 3 5) := by decide
  have h_2 : ¬(Nat.lcm 1 3 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 3 7) := by decide
  have h_3 : ¬(Nat.lcm 1 3 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 3 8) := by decide
  have h_4 : ¬(Nat.lcm 1 4 = Nat.lcm 1 5 ∧ Nat.lcm 1 5 = Nat.lcm 4 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R2 : Prop := ((¬(Nat.lcm 1 4 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 4 7) ∧ ¬(Nat.lcm 1 4 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 4 8)) ∧ (¬(Nat.lcm 1 5 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 5 7) ∧ (¬(Nat.lcm 1 5 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 5 8) ∧ ¬(Nat.lcm 1 7 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 7 8))))
theorem row2 : R2 := by
  have h_0 : ¬(Nat.lcm 1 4 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 4 7) := by decide
  have h_1 : ¬(Nat.lcm 1 4 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 4 8) := by decide
  have h_2 : ¬(Nat.lcm 1 5 = Nat.lcm 1 7 ∧ Nat.lcm 1 7 = Nat.lcm 5 7) := by decide
  have h_3 : ¬(Nat.lcm 1 5 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 5 8) := by decide
  have h_4 : ¬(Nat.lcm 1 7 = Nat.lcm 1 8 ∧ Nat.lcm 1 8 = Nat.lcm 7 8) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R3 : Prop := ((¬(Nat.lcm 2 3 = Nat.lcm 2 4 ∧ Nat.lcm 2 4 = Nat.lcm 3 4) ∧ ¬(Nat.lcm 2 3 = Nat.lcm 2 5 ∧ Nat.lcm 2 5 = Nat.lcm 3 5)) ∧ (¬(Nat.lcm 2 3 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 3 7) ∧ (¬(Nat.lcm 2 3 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 3 8) ∧ ¬(Nat.lcm 2 4 = Nat.lcm 2 5 ∧ Nat.lcm 2 5 = Nat.lcm 4 5))))
theorem row3 : R3 := by
  have h_0 : ¬(Nat.lcm 2 3 = Nat.lcm 2 4 ∧ Nat.lcm 2 4 = Nat.lcm 3 4) := by decide
  have h_1 : ¬(Nat.lcm 2 3 = Nat.lcm 2 5 ∧ Nat.lcm 2 5 = Nat.lcm 3 5) := by decide
  have h_2 : ¬(Nat.lcm 2 3 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 3 7) := by decide
  have h_3 : ¬(Nat.lcm 2 3 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 3 8) := by decide
  have h_4 : ¬(Nat.lcm 2 4 = Nat.lcm 2 5 ∧ Nat.lcm 2 5 = Nat.lcm 4 5) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R4 : Prop := ((¬(Nat.lcm 2 4 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 4 7) ∧ ¬(Nat.lcm 2 4 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 4 8)) ∧ (¬(Nat.lcm 2 5 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 5 7) ∧ (¬(Nat.lcm 2 5 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 5 8) ∧ ¬(Nat.lcm 2 7 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 7 8))))
theorem row4 : R4 := by
  have h_0 : ¬(Nat.lcm 2 4 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 4 7) := by decide
  have h_1 : ¬(Nat.lcm 2 4 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 4 8) := by decide
  have h_2 : ¬(Nat.lcm 2 5 = Nat.lcm 2 7 ∧ Nat.lcm 2 7 = Nat.lcm 5 7) := by decide
  have h_3 : ¬(Nat.lcm 2 5 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 5 8) := by decide
  have h_4 : ¬(Nat.lcm 2 7 = Nat.lcm 2 8 ∧ Nat.lcm 2 8 = Nat.lcm 7 8) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R5 : Prop := ((¬(Nat.lcm 3 4 = Nat.lcm 3 5 ∧ Nat.lcm 3 5 = Nat.lcm 4 5) ∧ ¬(Nat.lcm 3 4 = Nat.lcm 3 7 ∧ Nat.lcm 3 7 = Nat.lcm 4 7)) ∧ (¬(Nat.lcm 3 4 = Nat.lcm 3 8 ∧ Nat.lcm 3 8 = Nat.lcm 4 8) ∧ (¬(Nat.lcm 3 5 = Nat.lcm 3 7 ∧ Nat.lcm 3 7 = Nat.lcm 5 7) ∧ ¬(Nat.lcm 3 5 = Nat.lcm 3 8 ∧ Nat.lcm 3 8 = Nat.lcm 5 8))))
theorem row5 : R5 := by
  have h_0 : ¬(Nat.lcm 3 4 = Nat.lcm 3 5 ∧ Nat.lcm 3 5 = Nat.lcm 4 5) := by decide
  have h_1 : ¬(Nat.lcm 3 4 = Nat.lcm 3 7 ∧ Nat.lcm 3 7 = Nat.lcm 4 7) := by decide
  have h_2 : ¬(Nat.lcm 3 4 = Nat.lcm 3 8 ∧ Nat.lcm 3 8 = Nat.lcm 4 8) := by decide
  have h_3 : ¬(Nat.lcm 3 5 = Nat.lcm 3 7 ∧ Nat.lcm 3 7 = Nat.lcm 5 7) := by decide
  have h_4 : ¬(Nat.lcm 3 5 = Nat.lcm 3 8 ∧ Nat.lcm 3 8 = Nat.lcm 5 8) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R6 : Prop := ((¬(Nat.lcm 3 7 = Nat.lcm 3 8 ∧ Nat.lcm 3 8 = Nat.lcm 7 8) ∧ ¬(Nat.lcm 4 5 = Nat.lcm 4 7 ∧ Nat.lcm 4 7 = Nat.lcm 5 7)) ∧ (¬(Nat.lcm 4 5 = Nat.lcm 4 8 ∧ Nat.lcm 4 8 = Nat.lcm 5 8) ∧ (¬(Nat.lcm 4 7 = Nat.lcm 4 8 ∧ Nat.lcm 4 8 = Nat.lcm 7 8) ∧ ¬(Nat.lcm 5 7 = Nat.lcm 5 8 ∧ Nat.lcm 5 8 = Nat.lcm 7 8))))
theorem row6 : R6 := by
  have h_0 : ¬(Nat.lcm 3 7 = Nat.lcm 3 8 ∧ Nat.lcm 3 8 = Nat.lcm 7 8) := by decide
  have h_1 : ¬(Nat.lcm 4 5 = Nat.lcm 4 7 ∧ Nat.lcm 4 7 = Nat.lcm 5 7) := by decide
  have h_2 : ¬(Nat.lcm 4 5 = Nat.lcm 4 8 ∧ Nat.lcm 4 8 = Nat.lcm 5 8) := by decide
  have h_3 : ¬(Nat.lcm 4 7 = Nat.lcm 4 8 ∧ Nat.lcm 4 8 = Nat.lcm 7 8) := by decide
  have h_4 : ¬(Nat.lcm 5 7 = Nat.lcm 5 8 ∧ Nat.lcm 5 8 = Nat.lcm 7 8) := by decide
  exact ⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩

def R7 : Prop := ((((840 / 1 = 840) ∧ (840 / 2 = 420)) ∧ ((840 / 3 = 280) ∧ ((840 / 4 = 210) ∧ (840 / 5 = 168)))) ∧ (((840 / 7 = 120) ∧ ((840 / 8 = 105) ∧ (840 + 420 + 280 + 210 + 168 + 120 + 105 = 2143))) ∧ ((Nat.gcd 2143 840 = 1) ∧ ((1 ≥ 1) ∧ (8 ≤ 8)))))
theorem row7 : R7 := by
  have h_0 : (840 / 1 = 840) := by decide
  have h_1 : (840 / 2 = 420) := by decide
  have h_2 : (840 / 3 = 280) := by decide
  have h_3 : (840 / 4 = 210) := by decide
  have h_4 : (840 / 5 = 168) := by decide
  have h_5 : (840 / 7 = 120) := by decide
  have h_6 : (840 / 8 = 105) := by decide
  have h_7 : (840 + 420 + 280 + 210 + 168 + 120 + 105 = 2143) := by decide
  have h_8 : (Nat.gcd 2143 840 = 1) := by decide
  have h_9 : (1 ≥ 1) := by decide
  have h_10 : (8 ≤ 8) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, ⟨h_6, h_7⟩⟩, ⟨h_8, ⟨h_9, h_10⟩⟩⟩⟩

theorem jsp709 :
  (((R0 ∧ R1) ∧ (R2 ∧ R3)) ∧ ((R4 ∧ R5) ∧ (R6 ∧ R7))) := by
  exact ⟨⟨⟨row0, row1⟩, ⟨row2, row3⟩⟩, ⟨⟨row4, row5⟩, ⟨row6, row7⟩⟩⟩
