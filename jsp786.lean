-- =====================================================================
-- JSP-000786 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How long a run of consecutive integers can have pairwise
--       distinct divisor counts?
--       （连续整数最多能有多长的区间，其中各数的除数个数两两不同？）
--
-- 答案（构造下界）：至少 7。区间 [270, 276] 的除数个数为
--   270:16, 271:2, 272:10, 273:8, 274:4, 275:6, 276:12，两两不同。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp786.lean
-- =====================================================================

set_option maxRecDepth 1000000

/-- 计数 1..k 中整除 n 的除数个数（k = 0 时为 0）。-/
def divCountUpTo (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if (k + 1) ∣ n then 1 else 0) + divCountUpTo n k

/-- 正整数 n 的除数个数。-/
def divCount (n : Nat) : Nat := divCountUpTo n n

-- 闭项验证：divCount(270) = 16 等
example : divCount 270 = 16 := by decide
example : divCount 271 = 2 := by decide
example : divCount 272 = 10 := by decide
example : divCount 273 = 8 := by decide
example : divCount 274 = 4 := by decide
example : divCount 275 = 6 := by decide
example : divCount 276 = 12 := by decide

/-- 主定理：存在长度至少 7 的连续整数区间，其除数个数两两不同。
    构造：m = 270，长度 7（区间 [270, 276]）。 -/
theorem jsp786 :
    ∃ m : Nat, ∃ L : Nat,
      L ≥ 7 ∧ ∀ i : Nat, i < L → ∀ j : Nat, j < L → i ≠ j → divCount (m + i) ≠ divCount (m + j) := by
  refine ⟨270, 7, ?_⟩
  constructor
  · omega
  · intro i hi j hj hij
    have h0 : divCount 270 = 16 := by decide
    have h1 : divCount 271 = 2 := by decide
    have h2 : divCount 272 = 10 := by decide
    have h3 : divCount 273 = 8 := by decide
    have h4 : divCount 274 = 4 := by decide
    have h5 : divCount 275 = 6 := by decide
    have h6 : divCount 276 = 12 := by decide
    have hi7 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
    have hj7 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases hi7 with hi0 | hi1 | hi2 | hi3 | hi4 | hi5 | hi6 <;>
      rcases hj7 with hj0 | hj1 | hj2 | hj3 | hj4 | hj5 | hj6 <;>
        subst i <;> subst j <;> simp [h0, h1, h2, h3, h4, h5, h6] <;> omega
