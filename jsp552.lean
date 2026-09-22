-- =====================================================================
-- JSP-000552 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Near every integer, is there another integer whose least prime
--       factor exceeds the square of their distance?
--       （对任意整数 n，附近是否存在另一整数 m，其最小素因子大于
--         距离平方？）
--
-- 答案：是（平凡的）。对任意 n，取 m = n + 1（距离 1）：
--   任一素因子 p | m 满足 p ≥ 2 > 1 = 1² = (m−n)²，
--   故最小素因子 > 距离平方。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp552.lean
-- =====================================================================

set_option maxRecDepth 1000000

def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- 主定理：对任意 n ≥ 1，存在 m ≠ n 使所有素因子 p | m 满足
    p > (m−n)²。取 m = n + 1 即可。 -/
theorem jsp552 :
    ∀ n : Nat, n ≥ 1 → ∃ m : Nat, m ≠ n ∧ ∀ p : Nat, Prime p → p ∣ m → p > (m - n) * (m - n) := by
  intro n hn
  refine ⟨n + 1, ?_⟩
  constructor
  · omega
  · intro p hp hdiv
    have hge : p ≥ 2 := hp.1
    have hd : (n + 1 - n) * (n + 1 - n) = 1 := by
      have hsub : n + 1 - n = 1 := by omega
      simp [hsub]
    rw [hd]
    omega
