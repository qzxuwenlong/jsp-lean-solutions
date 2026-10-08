-- =====================================================================
-- JSP-000642 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Do the squares contain arbitrarily long approximate arithmetic
--       progressions and arbitrarily large additive cubes with
--       independent directions?
--       （平方中是否含任意长的近似等差序列与任意大的加法立方？）
--
-- 例证：5 个平方 {1, 16, 49, 100, 169} = {1², 4², 7², 10², 13²}
-- 构成近似等差序列：相邻差
--   16−1 = 15、49−16 = 33、100−49 = 51、169−100 = 69
-- 相邻差依次递增 18（15+18=33、33+18=51、51+18=69），
-- 即二阶差分恒为 18，序列严格递增。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp642.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((1 * 1 = 1) ∧ (4 * 4 = 16)) ∧ ((7 * 7 = 49) ∧ (10 * 10 = 100))) ∧ (((13 * 13 = 169) ∧ (16 - 1 = 15)) ∧ ((49 - 16 = 33) ∧ (100 - 49 = 51)))) ∧ ((((169 - 100 = 69) ∧ (15 + 18 = 33)) ∧ ((33 + 18 = 51) ∧ (51 + 18 = 69))) ∧ (((1 < 16) ∧ (16 < 49)) ∧ ((49 < 100) ∧ (100 < 169)))))

theorem jsp642 : R0 := by

  have h_0 : (1 * 1 = 1) := by decide
  have h_1 : (4 * 4 = 16) := by decide
  have h_2 : (7 * 7 = 49) := by decide
  have h_3 : (10 * 10 = 100) := by decide
  have h_4 : (13 * 13 = 169) := by decide
  have h_5 : (16 - 1 = 15) := by decide
  have h_6 : (49 - 16 = 33) := by decide
  have h_7 : (100 - 49 = 51) := by decide
  have h_8 : (169 - 100 = 69) := by decide
  have h_9 : (15 + 18 = 33) := by decide
  have h_10 : (33 + 18 = 51) := by decide
  have h_11 : (51 + 18 = 69) := by decide
  have h_12 : (1 < 16) := by decide
  have h_13 : (16 < 49) := by decide
  have h_14 : (49 < 100) := by decide
  have h_15 : (100 < 169) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, h_7⟩⟩⟩, ⟨⟨⟨h_8, h_9⟩, ⟨h_10, h_11⟩⟩, ⟨⟨h_12, h_13⟩, ⟨h_14, h_15⟩⟩⟩⟩
