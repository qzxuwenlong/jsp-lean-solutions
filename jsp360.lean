-- =====================================================================
-- JSP-000360 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can an integer set be if every pairwise least common
--       multiple is bounded by a prescribed value?
--       （若集合中任意两元素的最小公倍数被给定值所界定，
--         这样的整数集合能有多大？）
--
-- 构造：{1, 2, 3, 4, 6, 8, 12, 24} — 即 24 的全部 8 个正除数。
--       任意两个除数 a, b 都整除 24，故 lcm(a,b) 整除 24，
--       因而 lcm(a,b) ≤ 24。全部 28 对的最小公倍数逐一闭项核验。
--       答案：界 24 下可取到 8 个元素的集合（下界构造）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp360.lean
-- =====================================================================

set_option maxRecDepth 1000000

theorem jsp360 :
  ((((Nat.lcm 1 2 ≤ 24 ∧ (Nat.lcm 1 3 ≤ 24 ∧ Nat.lcm 1 4 ≤ 24)) ∧ ((Nat.lcm 1 6 ≤ 24 ∧ Nat.lcm 1 8 ≤ 24) ∧ (Nat.lcm 1 12 ≤ 24 ∧ Nat.lcm 1 24 ≤ 24))) ∧ ((Nat.lcm 2 3 ≤ 24 ∧ (Nat.lcm 2 4 ≤ 24 ∧ Nat.lcm 2 6 ≤ 24)) ∧ ((Nat.lcm 2 8 ≤ 24 ∧ Nat.lcm 2 12 ≤ 24) ∧ (Nat.lcm 2 24 ≤ 24 ∧ Nat.lcm 3 4 ≤ 24)))) ∧ (((Nat.lcm 3 6 ≤ 24 ∧ (Nat.lcm 3 8 ≤ 24 ∧ Nat.lcm 3 12 ≤ 24)) ∧ ((Nat.lcm 3 24 ≤ 24 ∧ Nat.lcm 4 6 ≤ 24) ∧ (Nat.lcm 4 8 ≤ 24 ∧ Nat.lcm 4 12 ≤ 24))) ∧ ((Nat.lcm 4 24 ≤ 24 ∧ (Nat.lcm 6 8 ≤ 24 ∧ Nat.lcm 6 12 ≤ 24)) ∧ ((Nat.lcm 6 24 ≤ 24 ∧ Nat.lcm 8 12 ≤ 24) ∧ (Nat.lcm 8 24 ≤ 24 ∧ Nat.lcm 12 24 ≤ 24))))) := by
  have h_0 : Nat.lcm 1 2 ≤ 24 := by decide
  have h_1 : Nat.lcm 1 3 ≤ 24 := by decide
  have h_2 : Nat.lcm 1 4 ≤ 24 := by decide
  have h_3 : Nat.lcm 1 6 ≤ 24 := by decide
  have h_4 : Nat.lcm 1 8 ≤ 24 := by decide
  have h_5 : Nat.lcm 1 12 ≤ 24 := by decide
  have h_6 : Nat.lcm 1 24 ≤ 24 := by decide
  have h_7 : Nat.lcm 2 3 ≤ 24 := by decide
  have h_8 : Nat.lcm 2 4 ≤ 24 := by decide
  have h_9 : Nat.lcm 2 6 ≤ 24 := by decide
  have h_10 : Nat.lcm 2 8 ≤ 24 := by decide
  have h_11 : Nat.lcm 2 12 ≤ 24 := by decide
  have h_12 : Nat.lcm 2 24 ≤ 24 := by decide
  have h_13 : Nat.lcm 3 4 ≤ 24 := by decide
  have h_14 : Nat.lcm 3 6 ≤ 24 := by decide
  have h_15 : Nat.lcm 3 8 ≤ 24 := by decide
  have h_16 : Nat.lcm 3 12 ≤ 24 := by decide
  have h_17 : Nat.lcm 3 24 ≤ 24 := by decide
  have h_18 : Nat.lcm 4 6 ≤ 24 := by decide
  have h_19 : Nat.lcm 4 8 ≤ 24 := by decide
  have h_20 : Nat.lcm 4 12 ≤ 24 := by decide
  have h_21 : Nat.lcm 4 24 ≤ 24 := by decide
  have h_22 : Nat.lcm 6 8 ≤ 24 := by decide
  have h_23 : Nat.lcm 6 12 ≤ 24 := by decide
  have h_24 : Nat.lcm 6 24 ≤ 24 := by decide
  have h_25 : Nat.lcm 8 12 ≤ 24 := by decide
  have h_26 : Nat.lcm 8 24 ≤ 24 := by decide
  have h_27 : Nat.lcm 12 24 ≤ 24 := by decide
  exact ⟨⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨⟨h_3, h_4⟩, ⟨h_5, h_6⟩⟩⟩, ⟨⟨h_7, ⟨h_8, h_9⟩⟩, ⟨⟨h_10, h_11⟩, ⟨h_12, h_13⟩⟩⟩⟩, ⟨⟨⟨h_14, ⟨h_15, h_16⟩⟩, ⟨⟨h_17, h_18⟩, ⟨h_19, h_20⟩⟩⟩, ⟨⟨h_21, ⟨h_22, h_23⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, h_27⟩⟩⟩⟩⟩
