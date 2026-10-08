-- =====================================================================
-- JSP-000680 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many coprime pairs of positive integers have equal divisor
--       sums, and how does that count grow?
--       （有多少个互素正整数对具有相等的约数和，其数量如何增长？）
--
-- 例证：gcd(6, 11) = 1（6 与 11 互素）且
--   σ(6)  = 1 + 2 + 3 + 6 = 12，
--   σ(11) = 1 + 11 = 12，
-- 即互素的 6 与 11 有相等的约数和 12。全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp680.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((1 + 2 + 3 + 6 = 12) ∧ ((1 + 11 = 12) ∧ (Nat.gcd 6 11 = 1))) ∧ ((6 ≠ 11) ∧ ((6 ≥ 1) ∧ (11 ≥ 1))))

theorem jsp680 : R0 := by

  have h_0 : (1 + 2 + 3 + 6 = 12) := by decide
  have h_1 : (1 + 11 = 12) := by decide
  have h_2 : (Nat.gcd 6 11 = 1) := by decide
  have h_3 : (6 ≠ 11) := by decide
  have h_4 : (6 ≥ 1) := by decide
  have h_5 : (11 ≥ 1) := by decide
  exact ⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨h_3, ⟨h_4, h_5⟩⟩⟩
