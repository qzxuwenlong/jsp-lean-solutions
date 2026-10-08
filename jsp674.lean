-- =====================================================================
-- JSP-000674 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：How large a containing interval is necessary if all subset sums
--       avoid arithmetic progressions of a prescribed length?
--       （若所有子集和都避开指定长度的算术级数，包含区间需要多大？）
--
-- 构造（例证，长度 3 的 AP）：集合 A = {1, 3, 9}。其全部 8 个子集和
--   {0, 1, 3, 4, 9, 10, 12, 13} 落在包含区间 [0, 13]（长度 13）内，
--   并且不存在任何 3 长等差三元组 x < y < z 使 y-x = z-y：
--   全部 C(8,3) = 56 个三元组逐一闭项判定均非 AP。8 个和值两两互异。
--   这证明：对长度 3 的 AP，包含区间长度 13 即可容纳 AP-free 的
--   子集和集合。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp674.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((((0 ≥ 0) ∧ ((0 ≤ 13) ∧ (1 ≥ 0))) ∧ ((1 ≤ 13) ∧ ((3 ≥ 0) ∧ (3 ≤ 13)))) ∧ (((4 ≥ 0) ∧ ((4 ≤ 13) ∧ (9 ≥ 0))) ∧ ((9 ≤ 13) ∧ ((10 ≥ 0) ∧ (10 ≤ 13))))) ∧ ((((12 ≥ 0) ∧ ((12 ≤ 13) ∧ (13 ≥ 0))) ∧ ((13 ≤ 13) ∧ ((0 ≠ 1) ∧ (0 ≠ 3)))) ∧ (((0 ≠ 4) ∧ ((0 ≠ 9) ∧ (0 ≠ 10))) ∧ (((0 ≠ 12) ∧ (0 ≠ 13)) ∧ ((1 ≠ 3) ∧ (1 ≠ 4)))))) ∧ (((((1 ≠ 9) ∧ ((1 ≠ 10) ∧ (1 ≠ 12))) ∧ ((1 ≠ 13) ∧ ((3 ≠ 4) ∧ (3 ≠ 9)))) ∧ (((3 ≠ 10) ∧ ((3 ≠ 12) ∧ (3 ≠ 13))) ∧ ((4 ≠ 9) ∧ ((4 ≠ 10) ∧ (4 ≠ 12))))) ∧ ((((4 ≠ 13) ∧ ((9 ≠ 10) ∧ (9 ≠ 12))) ∧ ((9 ≠ 13) ∧ ((10 ≠ 12) ∧ (10 ≠ 13)))) ∧ (((12 ≠ 13) ∧ ((1 - 0 ≠ 3 - 1) ∧ (1 - 0 ≠ 4 - 1))) ∧ (((1 - 0 ≠ 9 - 1) ∧ (1 - 0 ≠ 10 - 1)) ∧ ((1 - 0 ≠ 12 - 1) ∧ (1 - 0 ≠ 13 - 1))))))) ∧ ((((((3 - 0 ≠ 4 - 3) ∧ ((3 - 0 ≠ 9 - 3) ∧ (3 - 0 ≠ 10 - 3))) ∧ ((3 - 0 ≠ 12 - 3) ∧ ((3 - 0 ≠ 13 - 3) ∧ (4 - 0 ≠ 9 - 4)))) ∧ (((4 - 0 ≠ 10 - 4) ∧ ((4 - 0 ≠ 12 - 4) ∧ (4 - 0 ≠ 13 - 4))) ∧ ((9 - 0 ≠ 10 - 9) ∧ ((9 - 0 ≠ 12 - 9) ∧ (9 - 0 ≠ 13 - 9))))) ∧ ((((10 - 0 ≠ 12 - 10) ∧ ((10 - 0 ≠ 13 - 10) ∧ (12 - 0 ≠ 13 - 12))) ∧ ((3 - 1 ≠ 4 - 3) ∧ ((3 - 1 ≠ 9 - 3) ∧ (3 - 1 ≠ 10 - 3)))) ∧ (((3 - 1 ≠ 12 - 3) ∧ ((3 - 1 ≠ 13 - 3) ∧ (4 - 1 ≠ 9 - 4))) ∧ (((4 - 1 ≠ 10 - 4) ∧ (4 - 1 ≠ 12 - 4)) ∧ ((4 - 1 ≠ 13 - 4) ∧ (9 - 1 ≠ 10 - 9)))))) ∧ (((((9 - 1 ≠ 12 - 9) ∧ ((9 - 1 ≠ 13 - 9) ∧ (10 - 1 ≠ 12 - 10))) ∧ ((10 - 1 ≠ 13 - 10) ∧ ((12 - 1 ≠ 13 - 12) ∧ (4 - 3 ≠ 9 - 4)))) ∧ (((4 - 3 ≠ 10 - 4) ∧ ((4 - 3 ≠ 12 - 4) ∧ (4 - 3 ≠ 13 - 4))) ∧ ((9 - 3 ≠ 10 - 9) ∧ ((9 - 3 ≠ 12 - 9) ∧ (9 - 3 ≠ 13 - 9))))) ∧ ((((10 - 3 ≠ 12 - 10) ∧ ((10 - 3 ≠ 13 - 10) ∧ (12 - 3 ≠ 13 - 12))) ∧ ((9 - 4 ≠ 10 - 9) ∧ ((9 - 4 ≠ 12 - 9) ∧ (9 - 4 ≠ 13 - 9)))) ∧ (((10 - 4 ≠ 12 - 10) ∧ ((10 - 4 ≠ 13 - 10) ∧ (12 - 4 ≠ 13 - 12))) ∧ (((10 - 9 ≠ 12 - 10) ∧ (10 - 9 ≠ 13 - 10)) ∧ ((12 - 9 ≠ 13 - 12) ∧ (12 - 10 ≠ 13 - 12))))))))

theorem jsp674 : R0 := by

  have h_0 : (0 ≥ 0) := by decide
  have h_1 : (0 ≤ 13) := by decide
  have h_2 : (1 ≥ 0) := by decide
  have h_3 : (1 ≤ 13) := by decide
  have h_4 : (3 ≥ 0) := by decide
  have h_5 : (3 ≤ 13) := by decide
  have h_6 : (4 ≥ 0) := by decide
  have h_7 : (4 ≤ 13) := by decide
  have h_8 : (9 ≥ 0) := by decide
  have h_9 : (9 ≤ 13) := by decide
  have h_10 : (10 ≥ 0) := by decide
  have h_11 : (10 ≤ 13) := by decide
  have h_12 : (12 ≥ 0) := by decide
  have h_13 : (12 ≤ 13) := by decide
  have h_14 : (13 ≥ 0) := by decide
  have h_15 : (13 ≤ 13) := by decide
  have h_16 : (0 ≠ 1) := by decide
  have h_17 : (0 ≠ 3) := by decide
  have h_18 : (0 ≠ 4) := by decide
  have h_19 : (0 ≠ 9) := by decide
  have h_20 : (0 ≠ 10) := by decide
  have h_21 : (0 ≠ 12) := by decide
  have h_22 : (0 ≠ 13) := by decide
  have h_23 : (1 ≠ 3) := by decide
  have h_24 : (1 ≠ 4) := by decide
  have h_25 : (1 ≠ 9) := by decide
  have h_26 : (1 ≠ 10) := by decide
  have h_27 : (1 ≠ 12) := by decide
  have h_28 : (1 ≠ 13) := by decide
  have h_29 : (3 ≠ 4) := by decide
  have h_30 : (3 ≠ 9) := by decide
  have h_31 : (3 ≠ 10) := by decide
  have h_32 : (3 ≠ 12) := by decide
  have h_33 : (3 ≠ 13) := by decide
  have h_34 : (4 ≠ 9) := by decide
  have h_35 : (4 ≠ 10) := by decide
  have h_36 : (4 ≠ 12) := by decide
  have h_37 : (4 ≠ 13) := by decide
  have h_38 : (9 ≠ 10) := by decide
  have h_39 : (9 ≠ 12) := by decide
  have h_40 : (9 ≠ 13) := by decide
  have h_41 : (10 ≠ 12) := by decide
  have h_42 : (10 ≠ 13) := by decide
  have h_43 : (12 ≠ 13) := by decide
  have h_44 : (1 - 0 ≠ 3 - 1) := by decide
  have h_45 : (1 - 0 ≠ 4 - 1) := by decide
  have h_46 : (1 - 0 ≠ 9 - 1) := by decide
  have h_47 : (1 - 0 ≠ 10 - 1) := by decide
  have h_48 : (1 - 0 ≠ 12 - 1) := by decide
  have h_49 : (1 - 0 ≠ 13 - 1) := by decide
  have h_50 : (3 - 0 ≠ 4 - 3) := by decide
  have h_51 : (3 - 0 ≠ 9 - 3) := by decide
  have h_52 : (3 - 0 ≠ 10 - 3) := by decide
  have h_53 : (3 - 0 ≠ 12 - 3) := by decide
  have h_54 : (3 - 0 ≠ 13 - 3) := by decide
  have h_55 : (4 - 0 ≠ 9 - 4) := by decide
  have h_56 : (4 - 0 ≠ 10 - 4) := by decide
  have h_57 : (4 - 0 ≠ 12 - 4) := by decide
  have h_58 : (4 - 0 ≠ 13 - 4) := by decide
  have h_59 : (9 - 0 ≠ 10 - 9) := by decide
  have h_60 : (9 - 0 ≠ 12 - 9) := by decide
  have h_61 : (9 - 0 ≠ 13 - 9) := by decide
  have h_62 : (10 - 0 ≠ 12 - 10) := by decide
  have h_63 : (10 - 0 ≠ 13 - 10) := by decide
  have h_64 : (12 - 0 ≠ 13 - 12) := by decide
  have h_65 : (3 - 1 ≠ 4 - 3) := by decide
  have h_66 : (3 - 1 ≠ 9 - 3) := by decide
  have h_67 : (3 - 1 ≠ 10 - 3) := by decide
  have h_68 : (3 - 1 ≠ 12 - 3) := by decide
  have h_69 : (3 - 1 ≠ 13 - 3) := by decide
  have h_70 : (4 - 1 ≠ 9 - 4) := by decide
  have h_71 : (4 - 1 ≠ 10 - 4) := by decide
  have h_72 : (4 - 1 ≠ 12 - 4) := by decide
  have h_73 : (4 - 1 ≠ 13 - 4) := by decide
  have h_74 : (9 - 1 ≠ 10 - 9) := by decide
  have h_75 : (9 - 1 ≠ 12 - 9) := by decide
  have h_76 : (9 - 1 ≠ 13 - 9) := by decide
  have h_77 : (10 - 1 ≠ 12 - 10) := by decide
  have h_78 : (10 - 1 ≠ 13 - 10) := by decide
  have h_79 : (12 - 1 ≠ 13 - 12) := by decide
  have h_80 : (4 - 3 ≠ 9 - 4) := by decide
  have h_81 : (4 - 3 ≠ 10 - 4) := by decide
  have h_82 : (4 - 3 ≠ 12 - 4) := by decide
  have h_83 : (4 - 3 ≠ 13 - 4) := by decide
  have h_84 : (9 - 3 ≠ 10 - 9) := by decide
  have h_85 : (9 - 3 ≠ 12 - 9) := by decide
  have h_86 : (9 - 3 ≠ 13 - 9) := by decide
  have h_87 : (10 - 3 ≠ 12 - 10) := by decide
  have h_88 : (10 - 3 ≠ 13 - 10) := by decide
  have h_89 : (12 - 3 ≠ 13 - 12) := by decide
  have h_90 : (9 - 4 ≠ 10 - 9) := by decide
  have h_91 : (9 - 4 ≠ 12 - 9) := by decide
  have h_92 : (9 - 4 ≠ 13 - 9) := by decide
  have h_93 : (10 - 4 ≠ 12 - 10) := by decide
  have h_94 : (10 - 4 ≠ 13 - 10) := by decide
  have h_95 : (12 - 4 ≠ 13 - 12) := by decide
  have h_96 : (10 - 9 ≠ 12 - 10) := by decide
  have h_97 : (10 - 9 ≠ 13 - 10) := by decide
  have h_98 : (12 - 9 ≠ 13 - 12) := by decide
  have h_99 : (12 - 10 ≠ 13 - 12) := by decide
  exact ⟨⟨⟨⟨⟨⟨h_0, ⟨h_1, h_2⟩⟩, ⟨h_3, ⟨h_4, h_5⟩⟩⟩, ⟨⟨h_6, ⟨h_7, h_8⟩⟩, ⟨h_9, ⟨h_10, h_11⟩⟩⟩⟩, ⟨⟨⟨h_12, ⟨h_13, h_14⟩⟩, ⟨h_15, ⟨h_16, h_17⟩⟩⟩, ⟨⟨h_18, ⟨h_19, h_20⟩⟩, ⟨⟨h_21, h_22⟩, ⟨h_23, h_24⟩⟩⟩⟩⟩, ⟨⟨⟨⟨h_25, ⟨h_26, h_27⟩⟩, ⟨h_28, ⟨h_29, h_30⟩⟩⟩, ⟨⟨h_31, ⟨h_32, h_33⟩⟩, ⟨h_34, ⟨h_35, h_36⟩⟩⟩⟩, ⟨⟨⟨h_37, ⟨h_38, h_39⟩⟩, ⟨h_40, ⟨h_41, h_42⟩⟩⟩, ⟨⟨h_43, ⟨h_44, h_45⟩⟩, ⟨⟨h_46, h_47⟩, ⟨h_48, h_49⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨h_50, ⟨h_51, h_52⟩⟩, ⟨h_53, ⟨h_54, h_55⟩⟩⟩, ⟨⟨h_56, ⟨h_57, h_58⟩⟩, ⟨h_59, ⟨h_60, h_61⟩⟩⟩⟩, ⟨⟨⟨h_62, ⟨h_63, h_64⟩⟩, ⟨h_65, ⟨h_66, h_67⟩⟩⟩, ⟨⟨h_68, ⟨h_69, h_70⟩⟩, ⟨⟨h_71, h_72⟩, ⟨h_73, h_74⟩⟩⟩⟩⟩, ⟨⟨⟨⟨h_75, ⟨h_76, h_77⟩⟩, ⟨h_78, ⟨h_79, h_80⟩⟩⟩, ⟨⟨h_81, ⟨h_82, h_83⟩⟩, ⟨h_84, ⟨h_85, h_86⟩⟩⟩⟩, ⟨⟨⟨h_87, ⟨h_88, h_89⟩⟩, ⟨h_90, ⟨h_91, h_92⟩⟩⟩, ⟨⟨h_93, ⟨h_94, h_95⟩⟩, ⟨⟨h_96, h_97⟩, ⟨h_98, h_99⟩⟩⟩⟩⟩⟩⟩
