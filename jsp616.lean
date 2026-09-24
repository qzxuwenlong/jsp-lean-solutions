-- =====================================================================
-- JSP-000616 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How many sum-free subsets do the first several positive integers
--       have? Is their number approximately two to the power of half the
--       interval size?
--       （前若干个正整数有多少个 sum-free 子集？其数目是否近似于
--         区间大小一半的 2 次幂？）
--
-- 构造：区间 [1,5] 内全部 8 个"仅含奇数"的子集（含空集）都是
--       sum-free：奇数 + 奇数 = 偶数，而偶数不属于任何仅含奇数的
--       子集。子集数 = 2^3 = 8 = 2^ceil(5/2)，恰好给出题目所询
--       数量形态的下界（sum-free 子集数 ≥ 2^⌈n/2⌉）。
--       对每个子集掩码 m，逐对检查 [1,5]² 的全部 25 对 (a, b)：
--       a、b 均在子集内 ⇒ a+b 不在子集内（闭项机器核验 by decide）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp616.lean
-- =====================================================================

set_option maxRecDepth 1000000

/-- 掩码 m 的从 0 起的第 k 位（0 或 1）。 -/
def bit (k m : Nat) : Nat := (m / (2 ^ k)) % 2

def P_0 : Prop :=
  ((((((((((bit 1 0 = 1 → bit 1 0 = 1 → bit 2 0 = 0))) ∧ (((((bit 1 0 = 1 → bit 2 0 = 1 → bit 3 0 = 0))) ∧ (((bit 1 0 = 1 → bit 3 0 = 1 → bit 4 0 = 0))))))) ∧ (((((bit 1 0 = 1 → bit 4 0 = 1 → bit 5 0 = 0))) ∧ (((((bit 1 0 = 1 → bit 5 0 = 1 → bit 6 0 = 0))) ∧ (((bit 2 0 = 1 → bit 1 0 = 1 → bit 3 0 = 0))))))))) ∧ (((((((bit 2 0 = 1 → bit 2 0 = 1 → bit 4 0 = 0))) ∧ (((((bit 2 0 = 1 → bit 3 0 = 1 → bit 5 0 = 0))) ∧ (((bit 2 0 = 1 → bit 4 0 = 1 → bit 6 0 = 0))))))) ∧ (((((bit 2 0 = 1 → bit 5 0 = 1 → bit 7 0 = 0))) ∧ (((((bit 3 0 = 1 → bit 1 0 = 1 → bit 4 0 = 0))) ∧ (((bit 3 0 = 1 → bit 2 0 = 1 → bit 5 0 = 0))))))))))) ∧ (((((((((bit 3 0 = 1 → bit 3 0 = 1 → bit 6 0 = 0))) ∧ (((((bit 3 0 = 1 → bit 4 0 = 1 → bit 7 0 = 0))) ∧ (((bit 3 0 = 1 → bit 5 0 = 1 → bit 8 0 = 0))))))) ∧ (((((bit 4 0 = 1 → bit 1 0 = 1 → bit 5 0 = 0))) ∧ (((((bit 4 0 = 1 → bit 2 0 = 1 → bit 6 0 = 0))) ∧ (((bit 4 0 = 1 → bit 3 0 = 1 → bit 7 0 = 0))))))))) ∧ (((((((bit 4 0 = 1 → bit 4 0 = 1 → bit 8 0 = 0))) ∧ (((((bit 4 0 = 1 → bit 5 0 = 1 → bit 9 0 = 0))) ∧ (((bit 5 0 = 1 → bit 1 0 = 1 → bit 6 0 = 0))))))) ∧ (((((((bit 5 0 = 1 → bit 2 0 = 1 → bit 7 0 = 0))) ∧ (((bit 5 0 = 1 → bit 3 0 = 1 → bit 8 0 = 0))))) ∧ (((((bit 5 0 = 1 → bit 4 0 = 1 → bit 9 0 = 0))) ∧ (((bit 5 0 = 1 → bit 5 0 = 1 → bit 10 0 = 0))))))))))))

theorem sf_0 : P_0 := by
  have c_0_0 : (bit 1 0 = 1 → bit 1 0 = 1 → bit 2 0 = 0) := by decide
  have c_0_1 : (bit 1 0 = 1 → bit 2 0 = 1 → bit 3 0 = 0) := by decide
  have c_0_2 : (bit 1 0 = 1 → bit 3 0 = 1 → bit 4 0 = 0) := by decide
  have c_0_3 : (bit 1 0 = 1 → bit 4 0 = 1 → bit 5 0 = 0) := by decide
  have c_0_4 : (bit 1 0 = 1 → bit 5 0 = 1 → bit 6 0 = 0) := by decide
  have c_0_5 : (bit 2 0 = 1 → bit 1 0 = 1 → bit 3 0 = 0) := by decide
  have c_0_6 : (bit 2 0 = 1 → bit 2 0 = 1 → bit 4 0 = 0) := by decide
  have c_0_7 : (bit 2 0 = 1 → bit 3 0 = 1 → bit 5 0 = 0) := by decide
  have c_0_8 : (bit 2 0 = 1 → bit 4 0 = 1 → bit 6 0 = 0) := by decide
  have c_0_9 : (bit 2 0 = 1 → bit 5 0 = 1 → bit 7 0 = 0) := by decide
  have c_0_10 : (bit 3 0 = 1 → bit 1 0 = 1 → bit 4 0 = 0) := by decide
  have c_0_11 : (bit 3 0 = 1 → bit 2 0 = 1 → bit 5 0 = 0) := by decide
  have c_0_12 : (bit 3 0 = 1 → bit 3 0 = 1 → bit 6 0 = 0) := by decide
  have c_0_13 : (bit 3 0 = 1 → bit 4 0 = 1 → bit 7 0 = 0) := by decide
  have c_0_14 : (bit 3 0 = 1 → bit 5 0 = 1 → bit 8 0 = 0) := by decide
  have c_0_15 : (bit 4 0 = 1 → bit 1 0 = 1 → bit 5 0 = 0) := by decide
  have c_0_16 : (bit 4 0 = 1 → bit 2 0 = 1 → bit 6 0 = 0) := by decide
  have c_0_17 : (bit 4 0 = 1 → bit 3 0 = 1 → bit 7 0 = 0) := by decide
  have c_0_18 : (bit 4 0 = 1 → bit 4 0 = 1 → bit 8 0 = 0) := by decide
  have c_0_19 : (bit 4 0 = 1 → bit 5 0 = 1 → bit 9 0 = 0) := by decide
  have c_0_20 : (bit 5 0 = 1 → bit 1 0 = 1 → bit 6 0 = 0) := by decide
  have c_0_21 : (bit 5 0 = 1 → bit 2 0 = 1 → bit 7 0 = 0) := by decide
  have c_0_22 : (bit 5 0 = 1 → bit 3 0 = 1 → bit 8 0 = 0) := by decide
  have c_0_23 : (bit 5 0 = 1 → bit 4 0 = 1 → bit 9 0 = 0) := by decide
  have c_0_24 : (bit 5 0 = 1 → bit 5 0 = 1 → bit 10 0 = 0) := by decide
  exact ⟨⟨⟨⟨c_0_0, ⟨c_0_1, c_0_2⟩⟩, ⟨c_0_3, ⟨c_0_4, c_0_5⟩⟩⟩, ⟨⟨c_0_6, ⟨c_0_7, c_0_8⟩⟩, ⟨c_0_9, ⟨c_0_10, c_0_11⟩⟩⟩⟩, ⟨⟨⟨c_0_12, ⟨c_0_13, c_0_14⟩⟩, ⟨c_0_15, ⟨c_0_16, c_0_17⟩⟩⟩, ⟨⟨c_0_18, ⟨c_0_19, c_0_20⟩⟩, ⟨⟨c_0_21, c_0_22⟩, ⟨c_0_23, c_0_24⟩⟩⟩⟩⟩

def P_1 : Prop :=
  ((((((((((bit 1 2 = 1 → bit 1 2 = 1 → bit 2 2 = 0))) ∧ (((((bit 1 2 = 1 → bit 2 2 = 1 → bit 3 2 = 0))) ∧ (((bit 1 2 = 1 → bit 3 2 = 1 → bit 4 2 = 0))))))) ∧ (((((bit 1 2 = 1 → bit 4 2 = 1 → bit 5 2 = 0))) ∧ (((((bit 1 2 = 1 → bit 5 2 = 1 → bit 6 2 = 0))) ∧ (((bit 2 2 = 1 → bit 1 2 = 1 → bit 3 2 = 0))))))))) ∧ (((((((bit 2 2 = 1 → bit 2 2 = 1 → bit 4 2 = 0))) ∧ (((((bit 2 2 = 1 → bit 3 2 = 1 → bit 5 2 = 0))) ∧ (((bit 2 2 = 1 → bit 4 2 = 1 → bit 6 2 = 0))))))) ∧ (((((bit 2 2 = 1 → bit 5 2 = 1 → bit 7 2 = 0))) ∧ (((((bit 3 2 = 1 → bit 1 2 = 1 → bit 4 2 = 0))) ∧ (((bit 3 2 = 1 → bit 2 2 = 1 → bit 5 2 = 0))))))))))) ∧ (((((((((bit 3 2 = 1 → bit 3 2 = 1 → bit 6 2 = 0))) ∧ (((((bit 3 2 = 1 → bit 4 2 = 1 → bit 7 2 = 0))) ∧ (((bit 3 2 = 1 → bit 5 2 = 1 → bit 8 2 = 0))))))) ∧ (((((bit 4 2 = 1 → bit 1 2 = 1 → bit 5 2 = 0))) ∧ (((((bit 4 2 = 1 → bit 2 2 = 1 → bit 6 2 = 0))) ∧ (((bit 4 2 = 1 → bit 3 2 = 1 → bit 7 2 = 0))))))))) ∧ (((((((bit 4 2 = 1 → bit 4 2 = 1 → bit 8 2 = 0))) ∧ (((((bit 4 2 = 1 → bit 5 2 = 1 → bit 9 2 = 0))) ∧ (((bit 5 2 = 1 → bit 1 2 = 1 → bit 6 2 = 0))))))) ∧ (((((((bit 5 2 = 1 → bit 2 2 = 1 → bit 7 2 = 0))) ∧ (((bit 5 2 = 1 → bit 3 2 = 1 → bit 8 2 = 0))))) ∧ (((((bit 5 2 = 1 → bit 4 2 = 1 → bit 9 2 = 0))) ∧ (((bit 5 2 = 1 → bit 5 2 = 1 → bit 10 2 = 0))))))))))))

theorem sf_1 : P_1 := by
  have c_1_0 : (bit 1 2 = 1 → bit 1 2 = 1 → bit 2 2 = 0) := by decide
  have c_1_1 : (bit 1 2 = 1 → bit 2 2 = 1 → bit 3 2 = 0) := by decide
  have c_1_2 : (bit 1 2 = 1 → bit 3 2 = 1 → bit 4 2 = 0) := by decide
  have c_1_3 : (bit 1 2 = 1 → bit 4 2 = 1 → bit 5 2 = 0) := by decide
  have c_1_4 : (bit 1 2 = 1 → bit 5 2 = 1 → bit 6 2 = 0) := by decide
  have c_1_5 : (bit 2 2 = 1 → bit 1 2 = 1 → bit 3 2 = 0) := by decide
  have c_1_6 : (bit 2 2 = 1 → bit 2 2 = 1 → bit 4 2 = 0) := by decide
  have c_1_7 : (bit 2 2 = 1 → bit 3 2 = 1 → bit 5 2 = 0) := by decide
  have c_1_8 : (bit 2 2 = 1 → bit 4 2 = 1 → bit 6 2 = 0) := by decide
  have c_1_9 : (bit 2 2 = 1 → bit 5 2 = 1 → bit 7 2 = 0) := by decide
  have c_1_10 : (bit 3 2 = 1 → bit 1 2 = 1 → bit 4 2 = 0) := by decide
  have c_1_11 : (bit 3 2 = 1 → bit 2 2 = 1 → bit 5 2 = 0) := by decide
  have c_1_12 : (bit 3 2 = 1 → bit 3 2 = 1 → bit 6 2 = 0) := by decide
  have c_1_13 : (bit 3 2 = 1 → bit 4 2 = 1 → bit 7 2 = 0) := by decide
  have c_1_14 : (bit 3 2 = 1 → bit 5 2 = 1 → bit 8 2 = 0) := by decide
  have c_1_15 : (bit 4 2 = 1 → bit 1 2 = 1 → bit 5 2 = 0) := by decide
  have c_1_16 : (bit 4 2 = 1 → bit 2 2 = 1 → bit 6 2 = 0) := by decide
  have c_1_17 : (bit 4 2 = 1 → bit 3 2 = 1 → bit 7 2 = 0) := by decide
  have c_1_18 : (bit 4 2 = 1 → bit 4 2 = 1 → bit 8 2 = 0) := by decide
  have c_1_19 : (bit 4 2 = 1 → bit 5 2 = 1 → bit 9 2 = 0) := by decide
  have c_1_20 : (bit 5 2 = 1 → bit 1 2 = 1 → bit 6 2 = 0) := by decide
  have c_1_21 : (bit 5 2 = 1 → bit 2 2 = 1 → bit 7 2 = 0) := by decide
  have c_1_22 : (bit 5 2 = 1 → bit 3 2 = 1 → bit 8 2 = 0) := by decide
  have c_1_23 : (bit 5 2 = 1 → bit 4 2 = 1 → bit 9 2 = 0) := by decide
  have c_1_24 : (bit 5 2 = 1 → bit 5 2 = 1 → bit 10 2 = 0) := by decide
  exact ⟨⟨⟨⟨c_1_0, ⟨c_1_1, c_1_2⟩⟩, ⟨c_1_3, ⟨c_1_4, c_1_5⟩⟩⟩, ⟨⟨c_1_6, ⟨c_1_7, c_1_8⟩⟩, ⟨c_1_9, ⟨c_1_10, c_1_11⟩⟩⟩⟩, ⟨⟨⟨c_1_12, ⟨c_1_13, c_1_14⟩⟩, ⟨c_1_15, ⟨c_1_16, c_1_17⟩⟩⟩, ⟨⟨c_1_18, ⟨c_1_19, c_1_20⟩⟩, ⟨⟨c_1_21, c_1_22⟩, ⟨c_1_23, c_1_24⟩⟩⟩⟩⟩

def P_2 : Prop :=
  ((((((((((bit 1 8 = 1 → bit 1 8 = 1 → bit 2 8 = 0))) ∧ (((((bit 1 8 = 1 → bit 2 8 = 1 → bit 3 8 = 0))) ∧ (((bit 1 8 = 1 → bit 3 8 = 1 → bit 4 8 = 0))))))) ∧ (((((bit 1 8 = 1 → bit 4 8 = 1 → bit 5 8 = 0))) ∧ (((((bit 1 8 = 1 → bit 5 8 = 1 → bit 6 8 = 0))) ∧ (((bit 2 8 = 1 → bit 1 8 = 1 → bit 3 8 = 0))))))))) ∧ (((((((bit 2 8 = 1 → bit 2 8 = 1 → bit 4 8 = 0))) ∧ (((((bit 2 8 = 1 → bit 3 8 = 1 → bit 5 8 = 0))) ∧ (((bit 2 8 = 1 → bit 4 8 = 1 → bit 6 8 = 0))))))) ∧ (((((bit 2 8 = 1 → bit 5 8 = 1 → bit 7 8 = 0))) ∧ (((((bit 3 8 = 1 → bit 1 8 = 1 → bit 4 8 = 0))) ∧ (((bit 3 8 = 1 → bit 2 8 = 1 → bit 5 8 = 0))))))))))) ∧ (((((((((bit 3 8 = 1 → bit 3 8 = 1 → bit 6 8 = 0))) ∧ (((((bit 3 8 = 1 → bit 4 8 = 1 → bit 7 8 = 0))) ∧ (((bit 3 8 = 1 → bit 5 8 = 1 → bit 8 8 = 0))))))) ∧ (((((bit 4 8 = 1 → bit 1 8 = 1 → bit 5 8 = 0))) ∧ (((((bit 4 8 = 1 → bit 2 8 = 1 → bit 6 8 = 0))) ∧ (((bit 4 8 = 1 → bit 3 8 = 1 → bit 7 8 = 0))))))))) ∧ (((((((bit 4 8 = 1 → bit 4 8 = 1 → bit 8 8 = 0))) ∧ (((((bit 4 8 = 1 → bit 5 8 = 1 → bit 9 8 = 0))) ∧ (((bit 5 8 = 1 → bit 1 8 = 1 → bit 6 8 = 0))))))) ∧ (((((((bit 5 8 = 1 → bit 2 8 = 1 → bit 7 8 = 0))) ∧ (((bit 5 8 = 1 → bit 3 8 = 1 → bit 8 8 = 0))))) ∧ (((((bit 5 8 = 1 → bit 4 8 = 1 → bit 9 8 = 0))) ∧ (((bit 5 8 = 1 → bit 5 8 = 1 → bit 10 8 = 0))))))))))))

theorem sf_2 : P_2 := by
  have c_2_0 : (bit 1 8 = 1 → bit 1 8 = 1 → bit 2 8 = 0) := by decide
  have c_2_1 : (bit 1 8 = 1 → bit 2 8 = 1 → bit 3 8 = 0) := by decide
  have c_2_2 : (bit 1 8 = 1 → bit 3 8 = 1 → bit 4 8 = 0) := by decide
  have c_2_3 : (bit 1 8 = 1 → bit 4 8 = 1 → bit 5 8 = 0) := by decide
  have c_2_4 : (bit 1 8 = 1 → bit 5 8 = 1 → bit 6 8 = 0) := by decide
  have c_2_5 : (bit 2 8 = 1 → bit 1 8 = 1 → bit 3 8 = 0) := by decide
  have c_2_6 : (bit 2 8 = 1 → bit 2 8 = 1 → bit 4 8 = 0) := by decide
  have c_2_7 : (bit 2 8 = 1 → bit 3 8 = 1 → bit 5 8 = 0) := by decide
  have c_2_8 : (bit 2 8 = 1 → bit 4 8 = 1 → bit 6 8 = 0) := by decide
  have c_2_9 : (bit 2 8 = 1 → bit 5 8 = 1 → bit 7 8 = 0) := by decide
  have c_2_10 : (bit 3 8 = 1 → bit 1 8 = 1 → bit 4 8 = 0) := by decide
  have c_2_11 : (bit 3 8 = 1 → bit 2 8 = 1 → bit 5 8 = 0) := by decide
  have c_2_12 : (bit 3 8 = 1 → bit 3 8 = 1 → bit 6 8 = 0) := by decide
  have c_2_13 : (bit 3 8 = 1 → bit 4 8 = 1 → bit 7 8 = 0) := by decide
  have c_2_14 : (bit 3 8 = 1 → bit 5 8 = 1 → bit 8 8 = 0) := by decide
  have c_2_15 : (bit 4 8 = 1 → bit 1 8 = 1 → bit 5 8 = 0) := by decide
  have c_2_16 : (bit 4 8 = 1 → bit 2 8 = 1 → bit 6 8 = 0) := by decide
  have c_2_17 : (bit 4 8 = 1 → bit 3 8 = 1 → bit 7 8 = 0) := by decide
  have c_2_18 : (bit 4 8 = 1 → bit 4 8 = 1 → bit 8 8 = 0) := by decide
  have c_2_19 : (bit 4 8 = 1 → bit 5 8 = 1 → bit 9 8 = 0) := by decide
  have c_2_20 : (bit 5 8 = 1 → bit 1 8 = 1 → bit 6 8 = 0) := by decide
  have c_2_21 : (bit 5 8 = 1 → bit 2 8 = 1 → bit 7 8 = 0) := by decide
  have c_2_22 : (bit 5 8 = 1 → bit 3 8 = 1 → bit 8 8 = 0) := by decide
  have c_2_23 : (bit 5 8 = 1 → bit 4 8 = 1 → bit 9 8 = 0) := by decide
  have c_2_24 : (bit 5 8 = 1 → bit 5 8 = 1 → bit 10 8 = 0) := by decide
  exact ⟨⟨⟨⟨c_2_0, ⟨c_2_1, c_2_2⟩⟩, ⟨c_2_3, ⟨c_2_4, c_2_5⟩⟩⟩, ⟨⟨c_2_6, ⟨c_2_7, c_2_8⟩⟩, ⟨c_2_9, ⟨c_2_10, c_2_11⟩⟩⟩⟩, ⟨⟨⟨c_2_12, ⟨c_2_13, c_2_14⟩⟩, ⟨c_2_15, ⟨c_2_16, c_2_17⟩⟩⟩, ⟨⟨c_2_18, ⟨c_2_19, c_2_20⟩⟩, ⟨⟨c_2_21, c_2_22⟩, ⟨c_2_23, c_2_24⟩⟩⟩⟩⟩

def P_3 : Prop :=
  ((((((((((bit 1 32 = 1 → bit 1 32 = 1 → bit 2 32 = 0))) ∧ (((((bit 1 32 = 1 → bit 2 32 = 1 → bit 3 32 = 0))) ∧ (((bit 1 32 = 1 → bit 3 32 = 1 → bit 4 32 = 0))))))) ∧ (((((bit 1 32 = 1 → bit 4 32 = 1 → bit 5 32 = 0))) ∧ (((((bit 1 32 = 1 → bit 5 32 = 1 → bit 6 32 = 0))) ∧ (((bit 2 32 = 1 → bit 1 32 = 1 → bit 3 32 = 0))))))))) ∧ (((((((bit 2 32 = 1 → bit 2 32 = 1 → bit 4 32 = 0))) ∧ (((((bit 2 32 = 1 → bit 3 32 = 1 → bit 5 32 = 0))) ∧ (((bit 2 32 = 1 → bit 4 32 = 1 → bit 6 32 = 0))))))) ∧ (((((bit 2 32 = 1 → bit 5 32 = 1 → bit 7 32 = 0))) ∧ (((((bit 3 32 = 1 → bit 1 32 = 1 → bit 4 32 = 0))) ∧ (((bit 3 32 = 1 → bit 2 32 = 1 → bit 5 32 = 0))))))))))) ∧ (((((((((bit 3 32 = 1 → bit 3 32 = 1 → bit 6 32 = 0))) ∧ (((((bit 3 32 = 1 → bit 4 32 = 1 → bit 7 32 = 0))) ∧ (((bit 3 32 = 1 → bit 5 32 = 1 → bit 8 32 = 0))))))) ∧ (((((bit 4 32 = 1 → bit 1 32 = 1 → bit 5 32 = 0))) ∧ (((((bit 4 32 = 1 → bit 2 32 = 1 → bit 6 32 = 0))) ∧ (((bit 4 32 = 1 → bit 3 32 = 1 → bit 7 32 = 0))))))))) ∧ (((((((bit 4 32 = 1 → bit 4 32 = 1 → bit 8 32 = 0))) ∧ (((((bit 4 32 = 1 → bit 5 32 = 1 → bit 9 32 = 0))) ∧ (((bit 5 32 = 1 → bit 1 32 = 1 → bit 6 32 = 0))))))) ∧ (((((((bit 5 32 = 1 → bit 2 32 = 1 → bit 7 32 = 0))) ∧ (((bit 5 32 = 1 → bit 3 32 = 1 → bit 8 32 = 0))))) ∧ (((((bit 5 32 = 1 → bit 4 32 = 1 → bit 9 32 = 0))) ∧ (((bit 5 32 = 1 → bit 5 32 = 1 → bit 10 32 = 0))))))))))))

theorem sf_3 : P_3 := by
  have c_3_0 : (bit 1 32 = 1 → bit 1 32 = 1 → bit 2 32 = 0) := by decide
  have c_3_1 : (bit 1 32 = 1 → bit 2 32 = 1 → bit 3 32 = 0) := by decide
  have c_3_2 : (bit 1 32 = 1 → bit 3 32 = 1 → bit 4 32 = 0) := by decide
  have c_3_3 : (bit 1 32 = 1 → bit 4 32 = 1 → bit 5 32 = 0) := by decide
  have c_3_4 : (bit 1 32 = 1 → bit 5 32 = 1 → bit 6 32 = 0) := by decide
  have c_3_5 : (bit 2 32 = 1 → bit 1 32 = 1 → bit 3 32 = 0) := by decide
  have c_3_6 : (bit 2 32 = 1 → bit 2 32 = 1 → bit 4 32 = 0) := by decide
  have c_3_7 : (bit 2 32 = 1 → bit 3 32 = 1 → bit 5 32 = 0) := by decide
  have c_3_8 : (bit 2 32 = 1 → bit 4 32 = 1 → bit 6 32 = 0) := by decide
  have c_3_9 : (bit 2 32 = 1 → bit 5 32 = 1 → bit 7 32 = 0) := by decide
  have c_3_10 : (bit 3 32 = 1 → bit 1 32 = 1 → bit 4 32 = 0) := by decide
  have c_3_11 : (bit 3 32 = 1 → bit 2 32 = 1 → bit 5 32 = 0) := by decide
  have c_3_12 : (bit 3 32 = 1 → bit 3 32 = 1 → bit 6 32 = 0) := by decide
  have c_3_13 : (bit 3 32 = 1 → bit 4 32 = 1 → bit 7 32 = 0) := by decide
  have c_3_14 : (bit 3 32 = 1 → bit 5 32 = 1 → bit 8 32 = 0) := by decide
  have c_3_15 : (bit 4 32 = 1 → bit 1 32 = 1 → bit 5 32 = 0) := by decide
  have c_3_16 : (bit 4 32 = 1 → bit 2 32 = 1 → bit 6 32 = 0) := by decide
  have c_3_17 : (bit 4 32 = 1 → bit 3 32 = 1 → bit 7 32 = 0) := by decide
  have c_3_18 : (bit 4 32 = 1 → bit 4 32 = 1 → bit 8 32 = 0) := by decide
  have c_3_19 : (bit 4 32 = 1 → bit 5 32 = 1 → bit 9 32 = 0) := by decide
  have c_3_20 : (bit 5 32 = 1 → bit 1 32 = 1 → bit 6 32 = 0) := by decide
  have c_3_21 : (bit 5 32 = 1 → bit 2 32 = 1 → bit 7 32 = 0) := by decide
  have c_3_22 : (bit 5 32 = 1 → bit 3 32 = 1 → bit 8 32 = 0) := by decide
  have c_3_23 : (bit 5 32 = 1 → bit 4 32 = 1 → bit 9 32 = 0) := by decide
  have c_3_24 : (bit 5 32 = 1 → bit 5 32 = 1 → bit 10 32 = 0) := by decide
  exact ⟨⟨⟨⟨c_3_0, ⟨c_3_1, c_3_2⟩⟩, ⟨c_3_3, ⟨c_3_4, c_3_5⟩⟩⟩, ⟨⟨c_3_6, ⟨c_3_7, c_3_8⟩⟩, ⟨c_3_9, ⟨c_3_10, c_3_11⟩⟩⟩⟩, ⟨⟨⟨c_3_12, ⟨c_3_13, c_3_14⟩⟩, ⟨c_3_15, ⟨c_3_16, c_3_17⟩⟩⟩, ⟨⟨c_3_18, ⟨c_3_19, c_3_20⟩⟩, ⟨⟨c_3_21, c_3_22⟩, ⟨c_3_23, c_3_24⟩⟩⟩⟩⟩

def P_4 : Prop :=
  ((((((((((bit 1 10 = 1 → bit 1 10 = 1 → bit 2 10 = 0))) ∧ (((((bit 1 10 = 1 → bit 2 10 = 1 → bit 3 10 = 0))) ∧ (((bit 1 10 = 1 → bit 3 10 = 1 → bit 4 10 = 0))))))) ∧ (((((bit 1 10 = 1 → bit 4 10 = 1 → bit 5 10 = 0))) ∧ (((((bit 1 10 = 1 → bit 5 10 = 1 → bit 6 10 = 0))) ∧ (((bit 2 10 = 1 → bit 1 10 = 1 → bit 3 10 = 0))))))))) ∧ (((((((bit 2 10 = 1 → bit 2 10 = 1 → bit 4 10 = 0))) ∧ (((((bit 2 10 = 1 → bit 3 10 = 1 → bit 5 10 = 0))) ∧ (((bit 2 10 = 1 → bit 4 10 = 1 → bit 6 10 = 0))))))) ∧ (((((bit 2 10 = 1 → bit 5 10 = 1 → bit 7 10 = 0))) ∧ (((((bit 3 10 = 1 → bit 1 10 = 1 → bit 4 10 = 0))) ∧ (((bit 3 10 = 1 → bit 2 10 = 1 → bit 5 10 = 0))))))))))) ∧ (((((((((bit 3 10 = 1 → bit 3 10 = 1 → bit 6 10 = 0))) ∧ (((((bit 3 10 = 1 → bit 4 10 = 1 → bit 7 10 = 0))) ∧ (((bit 3 10 = 1 → bit 5 10 = 1 → bit 8 10 = 0))))))) ∧ (((((bit 4 10 = 1 → bit 1 10 = 1 → bit 5 10 = 0))) ∧ (((((bit 4 10 = 1 → bit 2 10 = 1 → bit 6 10 = 0))) ∧ (((bit 4 10 = 1 → bit 3 10 = 1 → bit 7 10 = 0))))))))) ∧ (((((((bit 4 10 = 1 → bit 4 10 = 1 → bit 8 10 = 0))) ∧ (((((bit 4 10 = 1 → bit 5 10 = 1 → bit 9 10 = 0))) ∧ (((bit 5 10 = 1 → bit 1 10 = 1 → bit 6 10 = 0))))))) ∧ (((((((bit 5 10 = 1 → bit 2 10 = 1 → bit 7 10 = 0))) ∧ (((bit 5 10 = 1 → bit 3 10 = 1 → bit 8 10 = 0))))) ∧ (((((bit 5 10 = 1 → bit 4 10 = 1 → bit 9 10 = 0))) ∧ (((bit 5 10 = 1 → bit 5 10 = 1 → bit 10 10 = 0))))))))))))

theorem sf_4 : P_4 := by
  have c_4_0 : (bit 1 10 = 1 → bit 1 10 = 1 → bit 2 10 = 0) := by decide
  have c_4_1 : (bit 1 10 = 1 → bit 2 10 = 1 → bit 3 10 = 0) := by decide
  have c_4_2 : (bit 1 10 = 1 → bit 3 10 = 1 → bit 4 10 = 0) := by decide
  have c_4_3 : (bit 1 10 = 1 → bit 4 10 = 1 → bit 5 10 = 0) := by decide
  have c_4_4 : (bit 1 10 = 1 → bit 5 10 = 1 → bit 6 10 = 0) := by decide
  have c_4_5 : (bit 2 10 = 1 → bit 1 10 = 1 → bit 3 10 = 0) := by decide
  have c_4_6 : (bit 2 10 = 1 → bit 2 10 = 1 → bit 4 10 = 0) := by decide
  have c_4_7 : (bit 2 10 = 1 → bit 3 10 = 1 → bit 5 10 = 0) := by decide
  have c_4_8 : (bit 2 10 = 1 → bit 4 10 = 1 → bit 6 10 = 0) := by decide
  have c_4_9 : (bit 2 10 = 1 → bit 5 10 = 1 → bit 7 10 = 0) := by decide
  have c_4_10 : (bit 3 10 = 1 → bit 1 10 = 1 → bit 4 10 = 0) := by decide
  have c_4_11 : (bit 3 10 = 1 → bit 2 10 = 1 → bit 5 10 = 0) := by decide
  have c_4_12 : (bit 3 10 = 1 → bit 3 10 = 1 → bit 6 10 = 0) := by decide
  have c_4_13 : (bit 3 10 = 1 → bit 4 10 = 1 → bit 7 10 = 0) := by decide
  have c_4_14 : (bit 3 10 = 1 → bit 5 10 = 1 → bit 8 10 = 0) := by decide
  have c_4_15 : (bit 4 10 = 1 → bit 1 10 = 1 → bit 5 10 = 0) := by decide
  have c_4_16 : (bit 4 10 = 1 → bit 2 10 = 1 → bit 6 10 = 0) := by decide
  have c_4_17 : (bit 4 10 = 1 → bit 3 10 = 1 → bit 7 10 = 0) := by decide
  have c_4_18 : (bit 4 10 = 1 → bit 4 10 = 1 → bit 8 10 = 0) := by decide
  have c_4_19 : (bit 4 10 = 1 → bit 5 10 = 1 → bit 9 10 = 0) := by decide
  have c_4_20 : (bit 5 10 = 1 → bit 1 10 = 1 → bit 6 10 = 0) := by decide
  have c_4_21 : (bit 5 10 = 1 → bit 2 10 = 1 → bit 7 10 = 0) := by decide
  have c_4_22 : (bit 5 10 = 1 → bit 3 10 = 1 → bit 8 10 = 0) := by decide
  have c_4_23 : (bit 5 10 = 1 → bit 4 10 = 1 → bit 9 10 = 0) := by decide
  have c_4_24 : (bit 5 10 = 1 → bit 5 10 = 1 → bit 10 10 = 0) := by decide
  exact ⟨⟨⟨⟨c_4_0, ⟨c_4_1, c_4_2⟩⟩, ⟨c_4_3, ⟨c_4_4, c_4_5⟩⟩⟩, ⟨⟨c_4_6, ⟨c_4_7, c_4_8⟩⟩, ⟨c_4_9, ⟨c_4_10, c_4_11⟩⟩⟩⟩, ⟨⟨⟨c_4_12, ⟨c_4_13, c_4_14⟩⟩, ⟨c_4_15, ⟨c_4_16, c_4_17⟩⟩⟩, ⟨⟨c_4_18, ⟨c_4_19, c_4_20⟩⟩, ⟨⟨c_4_21, c_4_22⟩, ⟨c_4_23, c_4_24⟩⟩⟩⟩⟩

def P_5 : Prop :=
  ((((((((((bit 1 34 = 1 → bit 1 34 = 1 → bit 2 34 = 0))) ∧ (((((bit 1 34 = 1 → bit 2 34 = 1 → bit 3 34 = 0))) ∧ (((bit 1 34 = 1 → bit 3 34 = 1 → bit 4 34 = 0))))))) ∧ (((((bit 1 34 = 1 → bit 4 34 = 1 → bit 5 34 = 0))) ∧ (((((bit 1 34 = 1 → bit 5 34 = 1 → bit 6 34 = 0))) ∧ (((bit 2 34 = 1 → bit 1 34 = 1 → bit 3 34 = 0))))))))) ∧ (((((((bit 2 34 = 1 → bit 2 34 = 1 → bit 4 34 = 0))) ∧ (((((bit 2 34 = 1 → bit 3 34 = 1 → bit 5 34 = 0))) ∧ (((bit 2 34 = 1 → bit 4 34 = 1 → bit 6 34 = 0))))))) ∧ (((((bit 2 34 = 1 → bit 5 34 = 1 → bit 7 34 = 0))) ∧ (((((bit 3 34 = 1 → bit 1 34 = 1 → bit 4 34 = 0))) ∧ (((bit 3 34 = 1 → bit 2 34 = 1 → bit 5 34 = 0))))))))))) ∧ (((((((((bit 3 34 = 1 → bit 3 34 = 1 → bit 6 34 = 0))) ∧ (((((bit 3 34 = 1 → bit 4 34 = 1 → bit 7 34 = 0))) ∧ (((bit 3 34 = 1 → bit 5 34 = 1 → bit 8 34 = 0))))))) ∧ (((((bit 4 34 = 1 → bit 1 34 = 1 → bit 5 34 = 0))) ∧ (((((bit 4 34 = 1 → bit 2 34 = 1 → bit 6 34 = 0))) ∧ (((bit 4 34 = 1 → bit 3 34 = 1 → bit 7 34 = 0))))))))) ∧ (((((((bit 4 34 = 1 → bit 4 34 = 1 → bit 8 34 = 0))) ∧ (((((bit 4 34 = 1 → bit 5 34 = 1 → bit 9 34 = 0))) ∧ (((bit 5 34 = 1 → bit 1 34 = 1 → bit 6 34 = 0))))))) ∧ (((((((bit 5 34 = 1 → bit 2 34 = 1 → bit 7 34 = 0))) ∧ (((bit 5 34 = 1 → bit 3 34 = 1 → bit 8 34 = 0))))) ∧ (((((bit 5 34 = 1 → bit 4 34 = 1 → bit 9 34 = 0))) ∧ (((bit 5 34 = 1 → bit 5 34 = 1 → bit 10 34 = 0))))))))))))

theorem sf_5 : P_5 := by
  have c_5_0 : (bit 1 34 = 1 → bit 1 34 = 1 → bit 2 34 = 0) := by decide
  have c_5_1 : (bit 1 34 = 1 → bit 2 34 = 1 → bit 3 34 = 0) := by decide
  have c_5_2 : (bit 1 34 = 1 → bit 3 34 = 1 → bit 4 34 = 0) := by decide
  have c_5_3 : (bit 1 34 = 1 → bit 4 34 = 1 → bit 5 34 = 0) := by decide
  have c_5_4 : (bit 1 34 = 1 → bit 5 34 = 1 → bit 6 34 = 0) := by decide
  have c_5_5 : (bit 2 34 = 1 → bit 1 34 = 1 → bit 3 34 = 0) := by decide
  have c_5_6 : (bit 2 34 = 1 → bit 2 34 = 1 → bit 4 34 = 0) := by decide
  have c_5_7 : (bit 2 34 = 1 → bit 3 34 = 1 → bit 5 34 = 0) := by decide
  have c_5_8 : (bit 2 34 = 1 → bit 4 34 = 1 → bit 6 34 = 0) := by decide
  have c_5_9 : (bit 2 34 = 1 → bit 5 34 = 1 → bit 7 34 = 0) := by decide
  have c_5_10 : (bit 3 34 = 1 → bit 1 34 = 1 → bit 4 34 = 0) := by decide
  have c_5_11 : (bit 3 34 = 1 → bit 2 34 = 1 → bit 5 34 = 0) := by decide
  have c_5_12 : (bit 3 34 = 1 → bit 3 34 = 1 → bit 6 34 = 0) := by decide
  have c_5_13 : (bit 3 34 = 1 → bit 4 34 = 1 → bit 7 34 = 0) := by decide
  have c_5_14 : (bit 3 34 = 1 → bit 5 34 = 1 → bit 8 34 = 0) := by decide
  have c_5_15 : (bit 4 34 = 1 → bit 1 34 = 1 → bit 5 34 = 0) := by decide
  have c_5_16 : (bit 4 34 = 1 → bit 2 34 = 1 → bit 6 34 = 0) := by decide
  have c_5_17 : (bit 4 34 = 1 → bit 3 34 = 1 → bit 7 34 = 0) := by decide
  have c_5_18 : (bit 4 34 = 1 → bit 4 34 = 1 → bit 8 34 = 0) := by decide
  have c_5_19 : (bit 4 34 = 1 → bit 5 34 = 1 → bit 9 34 = 0) := by decide
  have c_5_20 : (bit 5 34 = 1 → bit 1 34 = 1 → bit 6 34 = 0) := by decide
  have c_5_21 : (bit 5 34 = 1 → bit 2 34 = 1 → bit 7 34 = 0) := by decide
  have c_5_22 : (bit 5 34 = 1 → bit 3 34 = 1 → bit 8 34 = 0) := by decide
  have c_5_23 : (bit 5 34 = 1 → bit 4 34 = 1 → bit 9 34 = 0) := by decide
  have c_5_24 : (bit 5 34 = 1 → bit 5 34 = 1 → bit 10 34 = 0) := by decide
  exact ⟨⟨⟨⟨c_5_0, ⟨c_5_1, c_5_2⟩⟩, ⟨c_5_3, ⟨c_5_4, c_5_5⟩⟩⟩, ⟨⟨c_5_6, ⟨c_5_7, c_5_8⟩⟩, ⟨c_5_9, ⟨c_5_10, c_5_11⟩⟩⟩⟩, ⟨⟨⟨c_5_12, ⟨c_5_13, c_5_14⟩⟩, ⟨c_5_15, ⟨c_5_16, c_5_17⟩⟩⟩, ⟨⟨c_5_18, ⟨c_5_19, c_5_20⟩⟩, ⟨⟨c_5_21, c_5_22⟩, ⟨c_5_23, c_5_24⟩⟩⟩⟩⟩

def P_6 : Prop :=
  ((((((((((bit 1 40 = 1 → bit 1 40 = 1 → bit 2 40 = 0))) ∧ (((((bit 1 40 = 1 → bit 2 40 = 1 → bit 3 40 = 0))) ∧ (((bit 1 40 = 1 → bit 3 40 = 1 → bit 4 40 = 0))))))) ∧ (((((bit 1 40 = 1 → bit 4 40 = 1 → bit 5 40 = 0))) ∧ (((((bit 1 40 = 1 → bit 5 40 = 1 → bit 6 40 = 0))) ∧ (((bit 2 40 = 1 → bit 1 40 = 1 → bit 3 40 = 0))))))))) ∧ (((((((bit 2 40 = 1 → bit 2 40 = 1 → bit 4 40 = 0))) ∧ (((((bit 2 40 = 1 → bit 3 40 = 1 → bit 5 40 = 0))) ∧ (((bit 2 40 = 1 → bit 4 40 = 1 → bit 6 40 = 0))))))) ∧ (((((bit 2 40 = 1 → bit 5 40 = 1 → bit 7 40 = 0))) ∧ (((((bit 3 40 = 1 → bit 1 40 = 1 → bit 4 40 = 0))) ∧ (((bit 3 40 = 1 → bit 2 40 = 1 → bit 5 40 = 0))))))))))) ∧ (((((((((bit 3 40 = 1 → bit 3 40 = 1 → bit 6 40 = 0))) ∧ (((((bit 3 40 = 1 → bit 4 40 = 1 → bit 7 40 = 0))) ∧ (((bit 3 40 = 1 → bit 5 40 = 1 → bit 8 40 = 0))))))) ∧ (((((bit 4 40 = 1 → bit 1 40 = 1 → bit 5 40 = 0))) ∧ (((((bit 4 40 = 1 → bit 2 40 = 1 → bit 6 40 = 0))) ∧ (((bit 4 40 = 1 → bit 3 40 = 1 → bit 7 40 = 0))))))))) ∧ (((((((bit 4 40 = 1 → bit 4 40 = 1 → bit 8 40 = 0))) ∧ (((((bit 4 40 = 1 → bit 5 40 = 1 → bit 9 40 = 0))) ∧ (((bit 5 40 = 1 → bit 1 40 = 1 → bit 6 40 = 0))))))) ∧ (((((((bit 5 40 = 1 → bit 2 40 = 1 → bit 7 40 = 0))) ∧ (((bit 5 40 = 1 → bit 3 40 = 1 → bit 8 40 = 0))))) ∧ (((((bit 5 40 = 1 → bit 4 40 = 1 → bit 9 40 = 0))) ∧ (((bit 5 40 = 1 → bit 5 40 = 1 → bit 10 40 = 0))))))))))))

theorem sf_6 : P_6 := by
  have c_6_0 : (bit 1 40 = 1 → bit 1 40 = 1 → bit 2 40 = 0) := by decide
  have c_6_1 : (bit 1 40 = 1 → bit 2 40 = 1 → bit 3 40 = 0) := by decide
  have c_6_2 : (bit 1 40 = 1 → bit 3 40 = 1 → bit 4 40 = 0) := by decide
  have c_6_3 : (bit 1 40 = 1 → bit 4 40 = 1 → bit 5 40 = 0) := by decide
  have c_6_4 : (bit 1 40 = 1 → bit 5 40 = 1 → bit 6 40 = 0) := by decide
  have c_6_5 : (bit 2 40 = 1 → bit 1 40 = 1 → bit 3 40 = 0) := by decide
  have c_6_6 : (bit 2 40 = 1 → bit 2 40 = 1 → bit 4 40 = 0) := by decide
  have c_6_7 : (bit 2 40 = 1 → bit 3 40 = 1 → bit 5 40 = 0) := by decide
  have c_6_8 : (bit 2 40 = 1 → bit 4 40 = 1 → bit 6 40 = 0) := by decide
  have c_6_9 : (bit 2 40 = 1 → bit 5 40 = 1 → bit 7 40 = 0) := by decide
  have c_6_10 : (bit 3 40 = 1 → bit 1 40 = 1 → bit 4 40 = 0) := by decide
  have c_6_11 : (bit 3 40 = 1 → bit 2 40 = 1 → bit 5 40 = 0) := by decide
  have c_6_12 : (bit 3 40 = 1 → bit 3 40 = 1 → bit 6 40 = 0) := by decide
  have c_6_13 : (bit 3 40 = 1 → bit 4 40 = 1 → bit 7 40 = 0) := by decide
  have c_6_14 : (bit 3 40 = 1 → bit 5 40 = 1 → bit 8 40 = 0) := by decide
  have c_6_15 : (bit 4 40 = 1 → bit 1 40 = 1 → bit 5 40 = 0) := by decide
  have c_6_16 : (bit 4 40 = 1 → bit 2 40 = 1 → bit 6 40 = 0) := by decide
  have c_6_17 : (bit 4 40 = 1 → bit 3 40 = 1 → bit 7 40 = 0) := by decide
  have c_6_18 : (bit 4 40 = 1 → bit 4 40 = 1 → bit 8 40 = 0) := by decide
  have c_6_19 : (bit 4 40 = 1 → bit 5 40 = 1 → bit 9 40 = 0) := by decide
  have c_6_20 : (bit 5 40 = 1 → bit 1 40 = 1 → bit 6 40 = 0) := by decide
  have c_6_21 : (bit 5 40 = 1 → bit 2 40 = 1 → bit 7 40 = 0) := by decide
  have c_6_22 : (bit 5 40 = 1 → bit 3 40 = 1 → bit 8 40 = 0) := by decide
  have c_6_23 : (bit 5 40 = 1 → bit 4 40 = 1 → bit 9 40 = 0) := by decide
  have c_6_24 : (bit 5 40 = 1 → bit 5 40 = 1 → bit 10 40 = 0) := by decide
  exact ⟨⟨⟨⟨c_6_0, ⟨c_6_1, c_6_2⟩⟩, ⟨c_6_3, ⟨c_6_4, c_6_5⟩⟩⟩, ⟨⟨c_6_6, ⟨c_6_7, c_6_8⟩⟩, ⟨c_6_9, ⟨c_6_10, c_6_11⟩⟩⟩⟩, ⟨⟨⟨c_6_12, ⟨c_6_13, c_6_14⟩⟩, ⟨c_6_15, ⟨c_6_16, c_6_17⟩⟩⟩, ⟨⟨c_6_18, ⟨c_6_19, c_6_20⟩⟩, ⟨⟨c_6_21, c_6_22⟩, ⟨c_6_23, c_6_24⟩⟩⟩⟩⟩

def P_7 : Prop :=
  ((((((((((bit 1 42 = 1 → bit 1 42 = 1 → bit 2 42 = 0))) ∧ (((((bit 1 42 = 1 → bit 2 42 = 1 → bit 3 42 = 0))) ∧ (((bit 1 42 = 1 → bit 3 42 = 1 → bit 4 42 = 0))))))) ∧ (((((bit 1 42 = 1 → bit 4 42 = 1 → bit 5 42 = 0))) ∧ (((((bit 1 42 = 1 → bit 5 42 = 1 → bit 6 42 = 0))) ∧ (((bit 2 42 = 1 → bit 1 42 = 1 → bit 3 42 = 0))))))))) ∧ (((((((bit 2 42 = 1 → bit 2 42 = 1 → bit 4 42 = 0))) ∧ (((((bit 2 42 = 1 → bit 3 42 = 1 → bit 5 42 = 0))) ∧ (((bit 2 42 = 1 → bit 4 42 = 1 → bit 6 42 = 0))))))) ∧ (((((bit 2 42 = 1 → bit 5 42 = 1 → bit 7 42 = 0))) ∧ (((((bit 3 42 = 1 → bit 1 42 = 1 → bit 4 42 = 0))) ∧ (((bit 3 42 = 1 → bit 2 42 = 1 → bit 5 42 = 0))))))))))) ∧ (((((((((bit 3 42 = 1 → bit 3 42 = 1 → bit 6 42 = 0))) ∧ (((((bit 3 42 = 1 → bit 4 42 = 1 → bit 7 42 = 0))) ∧ (((bit 3 42 = 1 → bit 5 42 = 1 → bit 8 42 = 0))))))) ∧ (((((bit 4 42 = 1 → bit 1 42 = 1 → bit 5 42 = 0))) ∧ (((((bit 4 42 = 1 → bit 2 42 = 1 → bit 6 42 = 0))) ∧ (((bit 4 42 = 1 → bit 3 42 = 1 → bit 7 42 = 0))))))))) ∧ (((((((bit 4 42 = 1 → bit 4 42 = 1 → bit 8 42 = 0))) ∧ (((((bit 4 42 = 1 → bit 5 42 = 1 → bit 9 42 = 0))) ∧ (((bit 5 42 = 1 → bit 1 42 = 1 → bit 6 42 = 0))))))) ∧ (((((((bit 5 42 = 1 → bit 2 42 = 1 → bit 7 42 = 0))) ∧ (((bit 5 42 = 1 → bit 3 42 = 1 → bit 8 42 = 0))))) ∧ (((((bit 5 42 = 1 → bit 4 42 = 1 → bit 9 42 = 0))) ∧ (((bit 5 42 = 1 → bit 5 42 = 1 → bit 10 42 = 0))))))))))))

theorem sf_7 : P_7 := by
  have c_7_0 : (bit 1 42 = 1 → bit 1 42 = 1 → bit 2 42 = 0) := by decide
  have c_7_1 : (bit 1 42 = 1 → bit 2 42 = 1 → bit 3 42 = 0) := by decide
  have c_7_2 : (bit 1 42 = 1 → bit 3 42 = 1 → bit 4 42 = 0) := by decide
  have c_7_3 : (bit 1 42 = 1 → bit 4 42 = 1 → bit 5 42 = 0) := by decide
  have c_7_4 : (bit 1 42 = 1 → bit 5 42 = 1 → bit 6 42 = 0) := by decide
  have c_7_5 : (bit 2 42 = 1 → bit 1 42 = 1 → bit 3 42 = 0) := by decide
  have c_7_6 : (bit 2 42 = 1 → bit 2 42 = 1 → bit 4 42 = 0) := by decide
  have c_7_7 : (bit 2 42 = 1 → bit 3 42 = 1 → bit 5 42 = 0) := by decide
  have c_7_8 : (bit 2 42 = 1 → bit 4 42 = 1 → bit 6 42 = 0) := by decide
  have c_7_9 : (bit 2 42 = 1 → bit 5 42 = 1 → bit 7 42 = 0) := by decide
  have c_7_10 : (bit 3 42 = 1 → bit 1 42 = 1 → bit 4 42 = 0) := by decide
  have c_7_11 : (bit 3 42 = 1 → bit 2 42 = 1 → bit 5 42 = 0) := by decide
  have c_7_12 : (bit 3 42 = 1 → bit 3 42 = 1 → bit 6 42 = 0) := by decide
  have c_7_13 : (bit 3 42 = 1 → bit 4 42 = 1 → bit 7 42 = 0) := by decide
  have c_7_14 : (bit 3 42 = 1 → bit 5 42 = 1 → bit 8 42 = 0) := by decide
  have c_7_15 : (bit 4 42 = 1 → bit 1 42 = 1 → bit 5 42 = 0) := by decide
  have c_7_16 : (bit 4 42 = 1 → bit 2 42 = 1 → bit 6 42 = 0) := by decide
  have c_7_17 : (bit 4 42 = 1 → bit 3 42 = 1 → bit 7 42 = 0) := by decide
  have c_7_18 : (bit 4 42 = 1 → bit 4 42 = 1 → bit 8 42 = 0) := by decide
  have c_7_19 : (bit 4 42 = 1 → bit 5 42 = 1 → bit 9 42 = 0) := by decide
  have c_7_20 : (bit 5 42 = 1 → bit 1 42 = 1 → bit 6 42 = 0) := by decide
  have c_7_21 : (bit 5 42 = 1 → bit 2 42 = 1 → bit 7 42 = 0) := by decide
  have c_7_22 : (bit 5 42 = 1 → bit 3 42 = 1 → bit 8 42 = 0) := by decide
  have c_7_23 : (bit 5 42 = 1 → bit 4 42 = 1 → bit 9 42 = 0) := by decide
  have c_7_24 : (bit 5 42 = 1 → bit 5 42 = 1 → bit 10 42 = 0) := by decide
  exact ⟨⟨⟨⟨c_7_0, ⟨c_7_1, c_7_2⟩⟩, ⟨c_7_3, ⟨c_7_4, c_7_5⟩⟩⟩, ⟨⟨c_7_6, ⟨c_7_7, c_7_8⟩⟩, ⟨c_7_9, ⟨c_7_10, c_7_11⟩⟩⟩⟩, ⟨⟨⟨c_7_12, ⟨c_7_13, c_7_14⟩⟩, ⟨c_7_15, ⟨c_7_16, c_7_17⟩⟩⟩, ⟨⟨c_7_18, ⟨c_7_19, c_7_20⟩⟩, ⟨⟨c_7_21, c_7_22⟩, ⟨c_7_23, c_7_24⟩⟩⟩⟩⟩

theorem jsp616 :
  (((((((P_0)) ∧ ((P_1)))) ∧ ((((P_2)) ∧ ((P_3)))))) ∧ ((((((P_4)) ∧ ((P_5)))) ∧ ((((P_6)) ∧ ((P_7))))))) := by
  exact ⟨⟨⟨sf_0, sf_1⟩, ⟨sf_2, sf_3⟩⟩, ⟨⟨sf_4, sf_5⟩, ⟨sf_6, sf_7⟩⟩⟩
