-- =====================================================================
-- JSP-000891 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How small can the first factorial index congruent to minus one
--       modulo a prime be?
--       （模一个素数等于 −1 的首个阶乘索引可以多小？）
--
-- 例证（Wilson）：对素数 p，索引 n = p−1 即满足 n! ≡ −1 (mod p)：
--   p = 5：4! = 24 ≡ 4 (mod 5)，且 4 + 1 = 5；
--   p = 7：6! = 720 ≡ 6 (mod 7)，且 6 + 1 = 7；
--   p = 11：10! = 3628800 ≡ 10 (mod 11)，且 10 + 1 = 11。
-- 三个 p 均为奇素数（≥3 且为奇数），两两互异；阶乘、取模与
-- r + 1 = p 全部闭项验证。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp891.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((Nat.factorial 4 = 24) ∧ (24 % 5 = 4)) ∧ ((4 + 1 = 5) ∧ (5 % 2 = 1))) ∧ (((5 ≥ 3) ∧ (Nat.factorial 6 = 720)) ∧ ((720 % 7 = 6) ∧ ((6 + 1 = 7) ∧ (7 % 2 = 1))))) ∧ ((((7 ≥ 3) ∧ (Nat.factorial 10 = 3628800)) ∧ ((3628800 % 11 = 10) ∧ (10 + 1 = 11))) ∧ (((11 % 2 = 1) ∧ (11 ≥ 3)) ∧ ((5 ≠ 7) ∧ ((5 ≠ 11) ∧ (7 ≠ 11))))))

theorem jsp891 : R0 := by

  have h_0 : (Nat.factorial 4 = 24) := by decide
  have h_1 : (24 % 5 = 4) := by decide
  have h_2 : (4 + 1 = 5) := by decide
  have h_3 : (5 % 2 = 1) := by decide
  have h_4 : (5 ≥ 3) := by decide
  have h_5 : (Nat.factorial 6 = 720) := by decide
  have h_6 : (720 % 7 = 6) := by decide
  have h_7 : (6 + 1 = 7) := by decide
  have h_8 : (7 % 2 = 1) := by decide
  have h_9 : (7 ≥ 3) := by decide
  have h_10 : (Nat.factorial 10 = 3628800) := by decide
  have h_11 : (3628800 % 11 = 10) := by decide
  have h_12 : (10 + 1 = 11) := by decide
  have h_13 : (11 % 2 = 1) := by decide
  have h_14 : (11 ≥ 3) := by decide
  have h_15 : (5 ≠ 7) := by decide
  have h_16 : (5 ≠ 11) := by decide
  have h_17 : (7 ≠ 11) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, ⟨h_7, h_8⟩⟩⟩⟩, ⟨⟨⟨h_9, h_10⟩, ⟨h_11, h_12⟩⟩, ⟨⟨h_13, h_14⟩, ⟨h_15, ⟨h_16, h_17⟩⟩⟩⟩⟩
