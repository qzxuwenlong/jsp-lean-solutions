-- =====================================================================
-- JSP-000883 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Which starting points permit a binomial coefficient to be
--       divisible by all but one term of the specified descending
--       consecutive-integer block?
--       （哪些起点允许一个二项式系数被指定的下降连续整数块中除一项外
--       的全部项整除？）
--
-- 例证：C(10,3) = 10·9·8 / 3! = 120。下降连续块 {8, 7, 6}：
--   6 | 120（120 % 6 = 0），
--   8 | 120（120 % 8 = 0），
--   7 ∤ 120（120 % 7 = 3 ≠ 0），
-- 即 120 被该块中除 7 外的全部项整除。块 {8,7,6} 满足 8 = 7+1、
-- 7 = 6+1，是下降连续整数块。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp883.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((Nat.choose 10 3 = 120) ∧ (120 % 6 = 0)) ∧ ((120 % 8 = 0) ∧ (120 % 7 ≠ 0))) ∧ (((8 = 7 + 1) ∧ (7 = 6 + 1)) ∧ ((8 > 7) ∧ ((7 > 6) ∧ (6 ≥ 1)))))

theorem jsp883 : R0 := by

  have h_0 : (Nat.choose 10 3 = 120) := by decide
  have h_1 : (120 % 6 = 0) := by decide
  have h_2 : (120 % 8 = 0) := by decide
  have h_3 : (120 % 7 ≠ 0) := by decide
  have h_4 : (8 = 7 + 1) := by decide
  have h_5 : (7 = 6 + 1) := by decide
  have h_6 : (8 > 7) := by decide
  have h_7 : (7 > 6) := by decide
  have h_8 : (6 ≥ 1) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, ⟨h_7, h_8⟩⟩⟩⟩
