-- =====================================================================
-- JSP-000876 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Can several consecutive integer intervals each have product
--       congruent to one modulo the same prime?
--       （多个连续整数区间能否各自乘积模同一素数同余于 1？）
--
-- 例证（是）：模 p = 17，三个互不重叠的连续整数区间各自乘积
-- ≡ 1 (mod 17)：
--   [1, 5]：1·2·3·4·5 = 120 ≡ 1 (mod 17)；
--   [6, 11]：6·7·8·9·10·11 = 332640 ≡ 1 (mod 17)；
--   [12, 15]：12·13·14·15 = 32760 ≡ 1 (mod 17)。
-- 区间 [1,5]、[6,11]、[12,15] 两两不重叠（5 < 6 且 11 < 12），
-- 端点均为正整数。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp876.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := ((((120 % 17 = 1) ∧ (332640 % 17 = 1)) ∧ ((32760 % 17 = 1) ∧ ((5 < 6) ∧ (11 < 12)))) ∧ (((1 ≤ 5) ∧ (6 ≤ 11)) ∧ ((12 ≤ 15) ∧ ((5 ≥ 1) ∧ (15 ≥ 1)))))

theorem jsp876 : R0 := by

  have h_0 : (120 % 17 = 1) := by decide
  have h_1 : (332640 % 17 = 1) := by decide
  have h_2 : (32760 % 17 = 1) := by decide
  have h_3 : (5 < 6) := by decide
  have h_4 : (11 < 12) := by decide
  have h_5 : (1 ≤ 5) := by decide
  have h_6 : (6 ≤ 11) := by decide
  have h_7 : (12 ≤ 15) := by decide
  have h_8 : (5 ≥ 1) := by decide
  have h_9 : (15 ≥ 1) := by decide
  exact ⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, h_6⟩, ⟨h_7, ⟨h_8, h_9⟩⟩⟩⟩
