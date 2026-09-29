-- =====================================================================
-- JSP-001015 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：For pairwise coprime integers in an interval, how large can the
--       reciprocal sum of their distances to the endpoint be?
--       （区间内成对互质整数，到端点距离的倒数之和能多大？）
--
-- 构造：区间 [1,12]，上端点 12。取成对互质集合
--     A = {11, 10, 9, 7, 1}
--   （C(5,2)=10 对两两 gcd=1）。
--   到端点 12 的距离分别为 12-11=1, 12-10=2, 12-9=3, 12-7=5, 12-1=11，
--   其倒数之和为
--     1/1 + 1/2 + 1/3 + 1/5 + 1/11 = 701/330
--   （公共分母 lcm(1,2,3,5,11)=330；分子 330+165+110+66+30 = 701）。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp1015.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((Nat.gcd 11 10 = 1) ∧ (Nat.gcd 11 9 = 1)) ∧ ((Nat.gcd 11 7 = 1) ∧ ((Nat.gcd 11 1 = 1) ∧ (Nat.gcd 10 9 = 1)))) ∧ (((Nat.gcd 10 7 = 1) ∧ ((Nat.gcd 10 1 = 1) ∧ (Nat.gcd 9 7 = 1))) ∧ ((Nat.gcd 9 1 = 1) ∧ ((Nat.gcd 7 1 = 1) ∧ (12 - 11 = 1))))) ∧ ((((12 - 10 = 2) ∧ ((12 - 9 = 3) ∧ (12 - 7 = 5))) ∧ ((12 - 1 = 11) ∧ ((Nat.lcm (Nat.lcm (Nat.lcm (Nat.lcm 1 2) 3) 5) 11 = 330) ∧ (330 / 1 = 330)))) ∧ (((330 / 2 = 165) ∧ ((330 / 3 = 110) ∧ (330 / 5 = 66))) ∧ ((330 / 11 = 30) ∧ ((330 + 165 + 110 + 66 + 30 = 701) ∧ (330 * 701 = 701 * 330))))))

theorem jsp1015 : R0 := by

  have h_0 : (Nat.gcd 11 10 = 1) := by decide
  have h_1 : (Nat.gcd 11 9 = 1) := by decide
  have h_2 : (Nat.gcd 11 7 = 1) := by decide
  have h_3 : (Nat.gcd 11 1 = 1) := by decide
  have h_4 : (Nat.gcd 10 9 = 1) := by decide
  have h_5 : (Nat.gcd 10 7 = 1) := by decide
  have h_6 : (Nat.gcd 10 1 = 1) := by decide
  have h_7 : (Nat.gcd 9 7 = 1) := by decide
  have h_8 : (Nat.gcd 9 1 = 1) := by decide
  have h_9 : (Nat.gcd 7 1 = 1) := by decide
  have h_10 : (12 - 11 = 1) := by decide
  have h_11 : (12 - 10 = 2) := by decide
  have h_12 : (12 - 9 = 3) := by decide
  have h_13 : (12 - 7 = 5) := by decide
  have h_14 : (12 - 1 = 11) := by decide
  have h_15 : (Nat.lcm (Nat.lcm (Nat.lcm (Nat.lcm 1 2) 3) 5) 11 = 330) := by decide
  have h_16 : (330 / 1 = 330) := by decide
  have h_17 : (330 / 2 = 165) := by decide
  have h_18 : (330 / 3 = 110) := by decide
  have h_19 : (330 / 5 = 66) := by decide
  have h_20 : (330 / 11 = 30) := by decide
  have h_21 : (330 + 165 + 110 + 66 + 30 = 701) := by decide
  have h_22 : (330 * 701 = 701 * 330) := by decide
  exact ⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, ⟨h_6, h_7⟩⟩, ⟨h_8, ⟨h_9, h_10⟩⟩⟩⟩, ⟨⟨⟨h_11, ⟨h_12, h_13⟩⟩, ⟨h_14, ⟨h_15, h_16⟩⟩⟩, ⟨⟨h_17, ⟨h_18, h_19⟩⟩, ⟨h_20, ⟨h_21, h_22⟩⟩⟩⟩⟩
