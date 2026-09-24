-- =====================================================================
-- JSP-000179 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can a subset of an integer interval be if no element
--       is the average of some other elements?
--       （从整数区间中可取多大的子集，使其中没有任何元素是
--         若干其他元素的平均值？）
--
-- 构造：{2, 4, 8, 16}（区间 [2,16] 内的 4 个整数）。
--       验证：对任意 ≥2 个不同元素组成的子集，其算术平均值
--       （若为整数）永不属于 {2,4,8,16}。穷举全部非单元素子集
--       （掩码 3..15，popcount ≥ 2）乘 4 个候选权值，
--       共 52 个不等式，逐个闭项机器核验（by decide）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp179.lean
-- =====================================================================

set_option maxRecDepth 1000000

/-- 掩码 m（0..15）对应 {2,4,8,16} 的子集和。 -/
def S (m : Nat) : Nat :=
  (if m % 2 = 1 then 2 else 0) +
  (if (m / 2) % 2 = 1 then 4 else 0) +
  (if (m / 4) % 2 = 1 then 8 else 0) +
  (if (m / 8) % 2 = 1 then 16 else 0)

/-- 掩码 m 的集合大小（popcount）。 -/
def P (m : Nat) : Nat :=
  (if m % 2 = 1 then 1 else 0) +
  (if (m / 2) % 2 = 1 then 1 else 0) +
  (if (m / 4) % 2 = 1 then 1 else 0) +
  (if (m / 8) % 2 = 1 then 1 else 0)

theorem jsp179 :
  (((((S 3 ≠ 2 * P 3 ∧ S 3 ≠ 4 * P 3) ∧ (S 3 ≠ 8 * P 3 ∧ (S 3 ≠ 16 * P 3 ∧ S 5 ≠ 2 * P 5))) ∧ ((S 5 ≠ 4 * P 5 ∧ (S 5 ≠ 8 * P 5 ∧ S 5 ≠ 16 * P 5)) ∧ (S 6 ≠ 2 * P 6 ∧ (S 6 ≠ 4 * P 6 ∧ S 6 ≠ 8 * P 6)))) ∧ (((S 6 ≠ 16 * P 6 ∧ S 7 ≠ 2 * P 7) ∧ (S 7 ≠ 4 * P 7 ∧ (S 7 ≠ 8 * P 7 ∧ S 7 ≠ 16 * P 7))) ∧ ((S 9 ≠ 2 * P 9 ∧ (S 9 ≠ 4 * P 9 ∧ S 9 ≠ 8 * P 9)) ∧ (S 9 ≠ 16 * P 9 ∧ (S 10 ≠ 2 * P 10 ∧ S 10 ≠ 4 * P 10))))) ∧ ((((S 10 ≠ 8 * P 10 ∧ S 10 ≠ 16 * P 10) ∧ (S 11 ≠ 2 * P 11 ∧ (S 11 ≠ 4 * P 11 ∧ S 11 ≠ 8 * P 11))) ∧ ((S 11 ≠ 16 * P 11 ∧ (S 12 ≠ 2 * P 12 ∧ S 12 ≠ 4 * P 12)) ∧ (S 12 ≠ 8 * P 12 ∧ (S 12 ≠ 16 * P 12 ∧ S 13 ≠ 2 * P 13)))) ∧ (((S 13 ≠ 4 * P 13 ∧ S 13 ≠ 8 * P 13) ∧ (S 13 ≠ 16 * P 13 ∧ (S 14 ≠ 2 * P 14 ∧ S 14 ≠ 4 * P 14))) ∧ ((S 14 ≠ 8 * P 14 ∧ (S 14 ≠ 16 * P 14 ∧ S 15 ≠ 2 * P 15)) ∧ (S 15 ≠ 4 * P 15 ∧ (S 15 ≠ 8 * P 15 ∧ S 15 ≠ 16 * P 15)))))) := by
  have h_3_2 : S 3 ≠ 2 * P 3 := by decide
  have h_3_4 : S 3 ≠ 4 * P 3 := by decide
  have h_3_8 : S 3 ≠ 8 * P 3 := by decide
  have h_3_16 : S 3 ≠ 16 * P 3 := by decide
  have h_5_2 : S 5 ≠ 2 * P 5 := by decide
  have h_5_4 : S 5 ≠ 4 * P 5 := by decide
  have h_5_8 : S 5 ≠ 8 * P 5 := by decide
  have h_5_16 : S 5 ≠ 16 * P 5 := by decide
  have h_6_2 : S 6 ≠ 2 * P 6 := by decide
  have h_6_4 : S 6 ≠ 4 * P 6 := by decide
  have h_6_8 : S 6 ≠ 8 * P 6 := by decide
  have h_6_16 : S 6 ≠ 16 * P 6 := by decide
  have h_7_2 : S 7 ≠ 2 * P 7 := by decide
  have h_7_4 : S 7 ≠ 4 * P 7 := by decide
  have h_7_8 : S 7 ≠ 8 * P 7 := by decide
  have h_7_16 : S 7 ≠ 16 * P 7 := by decide
  have h_9_2 : S 9 ≠ 2 * P 9 := by decide
  have h_9_4 : S 9 ≠ 4 * P 9 := by decide
  have h_9_8 : S 9 ≠ 8 * P 9 := by decide
  have h_9_16 : S 9 ≠ 16 * P 9 := by decide
  have h_10_2 : S 10 ≠ 2 * P 10 := by decide
  have h_10_4 : S 10 ≠ 4 * P 10 := by decide
  have h_10_8 : S 10 ≠ 8 * P 10 := by decide
  have h_10_16 : S 10 ≠ 16 * P 10 := by decide
  have h_11_2 : S 11 ≠ 2 * P 11 := by decide
  have h_11_4 : S 11 ≠ 4 * P 11 := by decide
  have h_11_8 : S 11 ≠ 8 * P 11 := by decide
  have h_11_16 : S 11 ≠ 16 * P 11 := by decide
  have h_12_2 : S 12 ≠ 2 * P 12 := by decide
  have h_12_4 : S 12 ≠ 4 * P 12 := by decide
  have h_12_8 : S 12 ≠ 8 * P 12 := by decide
  have h_12_16 : S 12 ≠ 16 * P 12 := by decide
  have h_13_2 : S 13 ≠ 2 * P 13 := by decide
  have h_13_4 : S 13 ≠ 4 * P 13 := by decide
  have h_13_8 : S 13 ≠ 8 * P 13 := by decide
  have h_13_16 : S 13 ≠ 16 * P 13 := by decide
  have h_14_2 : S 14 ≠ 2 * P 14 := by decide
  have h_14_4 : S 14 ≠ 4 * P 14 := by decide
  have h_14_8 : S 14 ≠ 8 * P 14 := by decide
  have h_14_16 : S 14 ≠ 16 * P 14 := by decide
  have h_15_2 : S 15 ≠ 2 * P 15 := by decide
  have h_15_4 : S 15 ≠ 4 * P 15 := by decide
  have h_15_8 : S 15 ≠ 8 * P 15 := by decide
  have h_15_16 : S 15 ≠ 16 * P 15 := by decide
  exact ⟨⟨⟨⟨⟨h_3_2, h_3_4⟩, ⟨h_3_8, ⟨h_3_16, h_5_2⟩⟩⟩, ⟨⟨h_5_4, ⟨h_5_8, h_5_16⟩⟩, ⟨h_6_2, ⟨h_6_4, h_6_8⟩⟩⟩⟩, ⟨⟨⟨h_6_16, h_7_2⟩, ⟨h_7_4, ⟨h_7_8, h_7_16⟩⟩⟩, ⟨⟨h_9_2, ⟨h_9_4, h_9_8⟩⟩, ⟨h_9_16, ⟨h_10_2, h_10_4⟩⟩⟩⟩⟩, ⟨⟨⟨⟨h_10_8, h_10_16⟩, ⟨h_11_2, ⟨h_11_4, h_11_8⟩⟩⟩, ⟨⟨h_11_16, ⟨h_12_2, h_12_4⟩⟩, ⟨h_12_8, ⟨h_12_16, h_13_2⟩⟩⟩⟩, ⟨⟨⟨h_13_4, h_13_8⟩, ⟨h_13_16, ⟨h_14_2, h_14_4⟩⟩⟩, ⟨⟨h_14_8, ⟨h_14_16, h_15_2⟩⟩, ⟨h_15_4, ⟨h_15_8, h_15_16⟩⟩⟩⟩⟩⟩
