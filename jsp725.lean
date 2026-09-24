-- =====================================================================
-- JSP-000725 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large can an integer-interval subset be if subset sums using
--       different numbers of terms are never equal?
--       （整数区间子集可多大，若使用不同项数的子集和永不相等？）
--
-- 构造：{1, 2, 4, 8}（区间 [1,8] 内的 4 个整数，2 的幂）。
--       不同项数的子集和分属互不相交的集合：
--         1 项：{1, 2, 4, 8}
--         2 项：{3, 5, 6, 9, 10, 12}
--         3 项：{7, 11, 13, 14}
--         4 项：{15}
--       四组两两交集为空，故使用不同项数的子集和永不相等。
--       全部 38 对跨项数不等式闭项机器核验（by decide）。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp725.lean
-- =====================================================================

set_option maxRecDepth 1000000

/-- 掩码 m（1..15）对应 {1,2,4,8} 的子集和。 -/
def U (m : Nat) : Nat :=
  (if m % 2 = 1 then 1 else 0) +
  (if (m / 2) % 2 = 1 then 2 else 0) +
  (if (m / 4) % 2 = 1 then 4 else 0) +
  (if (m / 8) % 2 = 1 then 8 else 0)

theorem jsp725 :
  ((((((U 1 ≠ U 3 ∧ U 1 ≠ U 5) ∧ (U 1 ≠ U 6 ∧ U 1 ≠ U 9)) ∧ ((U 1 ≠ U 10 ∧ U 1 ≠ U 12) ∧ (U 2 ≠ U 3 ∧ (U 2 ≠ U 5 ∧ U 2 ≠ U 6)))) ∧ (((U 2 ≠ U 9 ∧ U 2 ≠ U 10) ∧ (U 2 ≠ U 12 ∧ (U 4 ≠ U 3 ∧ U 4 ≠ U 5))) ∧ ((U 4 ≠ U 6 ∧ U 4 ≠ U 9) ∧ (U 4 ≠ U 10 ∧ (U 4 ≠ U 12 ∧ U 8 ≠ U 3))))) ∧ ((((U 8 ≠ U 5 ∧ U 8 ≠ U 6) ∧ (U 8 ≠ U 9 ∧ (U 8 ≠ U 10 ∧ U 8 ≠ U 12))) ∧ ((U 1 ≠ U 7 ∧ U 1 ≠ U 11) ∧ (U 1 ≠ U 13 ∧ (U 1 ≠ U 14 ∧ U 2 ≠ U 7)))) ∧ (((U 2 ≠ U 11 ∧ U 2 ≠ U 13) ∧ (U 2 ≠ U 14 ∧ (U 4 ≠ U 7 ∧ U 4 ≠ U 11))) ∧ ((U 4 ≠ U 13 ∧ U 4 ≠ U 14) ∧ (U 8 ≠ U 7 ∧ (U 8 ≠ U 11 ∧ U 8 ≠ U 13)))))) ∧ (((((U 8 ≠ U 14 ∧ U 1 ≠ U 15) ∧ (U 2 ≠ U 15 ∧ U 4 ≠ U 15)) ∧ ((U 8 ≠ U 15 ∧ U 3 ≠ U 7) ∧ (U 3 ≠ U 11 ∧ (U 3 ≠ U 13 ∧ U 3 ≠ U 14)))) ∧ (((U 5 ≠ U 7 ∧ U 5 ≠ U 11) ∧ (U 5 ≠ U 13 ∧ (U 5 ≠ U 14 ∧ U 6 ≠ U 7))) ∧ ((U 6 ≠ U 11 ∧ U 6 ≠ U 13) ∧ (U 6 ≠ U 14 ∧ (U 9 ≠ U 7 ∧ U 9 ≠ U 11))))) ∧ ((((U 9 ≠ U 13 ∧ U 9 ≠ U 14) ∧ (U 10 ≠ U 7 ∧ (U 10 ≠ U 11 ∧ U 10 ≠ U 13))) ∧ ((U 10 ≠ U 14 ∧ U 12 ≠ U 7) ∧ (U 12 ≠ U 11 ∧ (U 12 ≠ U 13 ∧ U 12 ≠ U 14)))) ∧ (((U 3 ≠ U 15 ∧ U 5 ≠ U 15) ∧ (U 6 ≠ U 15 ∧ (U 9 ≠ U 15 ∧ U 10 ≠ U 15))) ∧ ((U 12 ≠ U 15 ∧ U 7 ≠ U 15) ∧ (U 11 ≠ U 15 ∧ (U 13 ≠ U 15 ∧ U 14 ≠ U 15))))))) := by
  have h_0 : U 1 ≠ U 3 := by decide
  have h_1 : U 1 ≠ U 5 := by decide
  have h_2 : U 1 ≠ U 6 := by decide
  have h_3 : U 1 ≠ U 9 := by decide
  have h_4 : U 1 ≠ U 10 := by decide
  have h_5 : U 1 ≠ U 12 := by decide
  have h_6 : U 2 ≠ U 3 := by decide
  have h_7 : U 2 ≠ U 5 := by decide
  have h_8 : U 2 ≠ U 6 := by decide
  have h_9 : U 2 ≠ U 9 := by decide
  have h_10 : U 2 ≠ U 10 := by decide
  have h_11 : U 2 ≠ U 12 := by decide
  have h_12 : U 4 ≠ U 3 := by decide
  have h_13 : U 4 ≠ U 5 := by decide
  have h_14 : U 4 ≠ U 6 := by decide
  have h_15 : U 4 ≠ U 9 := by decide
  have h_16 : U 4 ≠ U 10 := by decide
  have h_17 : U 4 ≠ U 12 := by decide
  have h_18 : U 8 ≠ U 3 := by decide
  have h_19 : U 8 ≠ U 5 := by decide
  have h_20 : U 8 ≠ U 6 := by decide
  have h_21 : U 8 ≠ U 9 := by decide
  have h_22 : U 8 ≠ U 10 := by decide
  have h_23 : U 8 ≠ U 12 := by decide
  have h_24 : U 1 ≠ U 7 := by decide
  have h_25 : U 1 ≠ U 11 := by decide
  have h_26 : U 1 ≠ U 13 := by decide
  have h_27 : U 1 ≠ U 14 := by decide
  have h_28 : U 2 ≠ U 7 := by decide
  have h_29 : U 2 ≠ U 11 := by decide
  have h_30 : U 2 ≠ U 13 := by decide
  have h_31 : U 2 ≠ U 14 := by decide
  have h_32 : U 4 ≠ U 7 := by decide
  have h_33 : U 4 ≠ U 11 := by decide
  have h_34 : U 4 ≠ U 13 := by decide
  have h_35 : U 4 ≠ U 14 := by decide
  have h_36 : U 8 ≠ U 7 := by decide
  have h_37 : U 8 ≠ U 11 := by decide
  have h_38 : U 8 ≠ U 13 := by decide
  have h_39 : U 8 ≠ U 14 := by decide
  have h_40 : U 1 ≠ U 15 := by decide
  have h_41 : U 2 ≠ U 15 := by decide
  have h_42 : U 4 ≠ U 15 := by decide
  have h_43 : U 8 ≠ U 15 := by decide
  have h_44 : U 3 ≠ U 7 := by decide
  have h_45 : U 3 ≠ U 11 := by decide
  have h_46 : U 3 ≠ U 13 := by decide
  have h_47 : U 3 ≠ U 14 := by decide
  have h_48 : U 5 ≠ U 7 := by decide
  have h_49 : U 5 ≠ U 11 := by decide
  have h_50 : U 5 ≠ U 13 := by decide
  have h_51 : U 5 ≠ U 14 := by decide
  have h_52 : U 6 ≠ U 7 := by decide
  have h_53 : U 6 ≠ U 11 := by decide
  have h_54 : U 6 ≠ U 13 := by decide
  have h_55 : U 6 ≠ U 14 := by decide
  have h_56 : U 9 ≠ U 7 := by decide
  have h_57 : U 9 ≠ U 11 := by decide
  have h_58 : U 9 ≠ U 13 := by decide
  have h_59 : U 9 ≠ U 14 := by decide
  have h_60 : U 10 ≠ U 7 := by decide
  have h_61 : U 10 ≠ U 11 := by decide
  have h_62 : U 10 ≠ U 13 := by decide
  have h_63 : U 10 ≠ U 14 := by decide
  have h_64 : U 12 ≠ U 7 := by decide
  have h_65 : U 12 ≠ U 11 := by decide
  have h_66 : U 12 ≠ U 13 := by decide
  have h_67 : U 12 ≠ U 14 := by decide
  have h_68 : U 3 ≠ U 15 := by decide
  have h_69 : U 5 ≠ U 15 := by decide
  have h_70 : U 6 ≠ U 15 := by decide
  have h_71 : U 9 ≠ U 15 := by decide
  have h_72 : U 10 ≠ U 15 := by decide
  have h_73 : U 12 ≠ U 15 := by decide
  have h_74 : U 7 ≠ U 15 := by decide
  have h_75 : U 11 ≠ U 15 := by decide
  have h_76 : U 13 ≠ U 15 := by decide
  have h_77 : U 14 ≠ U 15 := by decide
  exact ⟨⟨⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, h_3⟩⟩, ⟨⟨h_4, h_5⟩, ⟨h_6, ⟨h_7, h_8⟩⟩⟩⟩, ⟨⟨⟨h_9, h_10⟩, ⟨h_11, ⟨h_12, h_13⟩⟩⟩, ⟨⟨h_14, h_15⟩, ⟨h_16, ⟨h_17, h_18⟩⟩⟩⟩⟩, ⟨⟨⟨⟨h_19, h_20⟩, ⟨h_21, ⟨h_22, h_23⟩⟩⟩, ⟨⟨h_24, h_25⟩, ⟨h_26, ⟨h_27, h_28⟩⟩⟩⟩, ⟨⟨⟨h_29, h_30⟩, ⟨h_31, ⟨h_32, h_33⟩⟩⟩, ⟨⟨h_34, h_35⟩, ⟨h_36, ⟨h_37, h_38⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨h_39, h_40⟩, ⟨h_41, h_42⟩⟩, ⟨⟨h_43, h_44⟩, ⟨h_45, ⟨h_46, h_47⟩⟩⟩⟩, ⟨⟨⟨h_48, h_49⟩, ⟨h_50, ⟨h_51, h_52⟩⟩⟩, ⟨⟨h_53, h_54⟩, ⟨h_55, ⟨h_56, h_57⟩⟩⟩⟩⟩, ⟨⟨⟨⟨h_58, h_59⟩, ⟨h_60, ⟨h_61, h_62⟩⟩⟩, ⟨⟨h_63, h_64⟩, ⟨h_65, ⟨h_66, h_67⟩⟩⟩⟩, ⟨⟨⟨h_68, h_69⟩, ⟨h_70, ⟨h_71, h_72⟩⟩⟩, ⟨⟨h_73, h_74⟩, ⟨h_75, ⟨h_76, h_77⟩⟩⟩⟩⟩⟩⟩
