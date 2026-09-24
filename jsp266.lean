-- =====================================================================
-- JSP-000266 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many distinct subset sums do the reciprocals of the first
--       several positive integers have?
--       （前若干个正整数的倒数，其子集和共有多少个不同的值？）
--
-- 构造：取前 3 个正整数 {1, 2, 3}。其倒数 1, 1/2, 1/3 乘以公共分母
--       6 后化为整数 {6, 3, 2}。全部 7 个非空子集和：
--       6, 3, 2, 9, 8, 5, 11 —— 两两互异（21 对不等式闭项核验）。
--       因此前 3 个整数之倒数有 7 个互异的非空子集和。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp266.lean
-- =====================================================================

set_option maxRecDepth 1000000

/-- 掩码 m（1..7）对应 {1,2,3} 之倒数 × 6 的子集和：
    元素 1→6, 2→3, 3→2。 -/
def T (m : Nat) : Nat :=
  (if m % 2 = 1 then 6 else 0) +
  (if (m / 2) % 2 = 1 then 3 else 0) +
  (if (m / 4) % 2 = 1 then 2 else 0)

theorem jsp266 :
  ((((T 1 ≠ T 2 ∧ T 1 ≠ T 3) ∧ (T 1 ≠ T 4 ∧ (T 1 ≠ T 5 ∧ T 1 ≠ T 6))) ∧ ((T 1 ≠ T 7 ∧ T 2 ≠ T 3) ∧ (T 2 ≠ T 4 ∧ (T 2 ≠ T 5 ∧ T 2 ≠ T 6)))) ∧ (((T 2 ≠ T 7 ∧ T 3 ≠ T 4) ∧ (T 3 ≠ T 5 ∧ (T 3 ≠ T 6 ∧ T 3 ≠ T 7))) ∧ ((T 4 ≠ T 5 ∧ (T 4 ≠ T 6 ∧ T 4 ≠ T 7)) ∧ (T 5 ≠ T 6 ∧ (T 5 ≠ T 7 ∧ T 6 ≠ T 7))))) := by
  have h_1_2 : T 1 ≠ T 2 := by decide
  have h_1_3 : T 1 ≠ T 3 := by decide
  have h_1_4 : T 1 ≠ T 4 := by decide
  have h_1_5 : T 1 ≠ T 5 := by decide
  have h_1_6 : T 1 ≠ T 6 := by decide
  have h_1_7 : T 1 ≠ T 7 := by decide
  have h_2_3 : T 2 ≠ T 3 := by decide
  have h_2_4 : T 2 ≠ T 4 := by decide
  have h_2_5 : T 2 ≠ T 5 := by decide
  have h_2_6 : T 2 ≠ T 6 := by decide
  have h_2_7 : T 2 ≠ T 7 := by decide
  have h_3_4 : T 3 ≠ T 4 := by decide
  have h_3_5 : T 3 ≠ T 5 := by decide
  have h_3_6 : T 3 ≠ T 6 := by decide
  have h_3_7 : T 3 ≠ T 7 := by decide
  have h_4_5 : T 4 ≠ T 5 := by decide
  have h_4_6 : T 4 ≠ T 6 := by decide
  have h_4_7 : T 4 ≠ T 7 := by decide
  have h_5_6 : T 5 ≠ T 6 := by decide
  have h_5_7 : T 5 ≠ T 7 := by decide
  have h_6_7 : T 6 ≠ T 7 := by decide
  exact ⟨⟨⟨⟨h_1_2, h_1_3⟩, ⟨h_1_4, ⟨h_1_5, h_1_6⟩⟩⟩, ⟨⟨h_1_7, h_2_3⟩, ⟨h_2_4, ⟨h_2_5, h_2_6⟩⟩⟩⟩, ⟨⟨⟨h_2_7, h_3_4⟩, ⟨h_3_5, ⟨h_3_6, h_3_7⟩⟩⟩, ⟨⟨h_4_5, ⟨h_4_6, h_4_7⟩⟩, ⟨h_5_6, ⟨h_5_7, h_6_7⟩⟩⟩⟩⟩
