-- =====================================================================
-- JSP-000941 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：Does repeatedly halving even integers and replacing odd integers
--       by three times the integer plus one eventually reach the value one?
--       （反复对偶数取半、对奇数取 3n+1，是否最终到达 1？）
--
-- 例证：从 7 出发的迭代轨迹为
--   7 → 22 → 11 → 34 → 17 → 52 → 26 → 13 → 40 → 20 → 10 → 5 → 16 → 8
--   → 4 → 2 → 1
-- 每一步的规则闭项验证：奇数 n 时 3n+1（22=3·7+1、34=3·11+1、
-- 52=3·17+1、40=3·13+1、16=3·5+1），偶数 n 时 n/2（11=22/2、
-- 17=34/2、26=52/2、13=26/2、20=40/2、10=20/2、5=10/2、8=16/2、
-- 4=8/2、2=4/2、1=2/2）；全部中间值 ≥ 1，最终到达 1。
--   全部闭项 by decide。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp941.lean
-- =====================================================================

set_option maxRecDepth 1000000

def R0 : Prop := (((((((7 % 2 = 1 ∨ 7 % 2 = 0) ∧ (3 * 7 + 1 = 22)) ∧ ((7 % 2 = 1) ∧ ((7 ≥ 1) ∧ (22 ≥ 1)))) ∧ (((22 % 2 = 1 ∨ 22 % 2 = 0) ∧ (22 / 2 = 11)) ∧ ((22 % 2 = 0) ∧ ((22 ≥ 1) ∧ (11 ≥ 1))))) ∧ ((((11 % 2 = 1 ∨ 11 % 2 = 0) ∧ (3 * 11 + 1 = 34)) ∧ ((11 % 2 = 1) ∧ ((11 ≥ 1) ∧ (34 ≥ 1)))) ∧ (((34 % 2 = 1 ∨ 34 % 2 = 0) ∧ (34 / 2 = 17)) ∧ ((34 % 2 = 0) ∧ ((34 ≥ 1) ∧ (17 ≥ 1)))))) ∧ (((((17 % 2 = 1 ∨ 17 % 2 = 0) ∧ (3 * 17 + 1 = 52)) ∧ ((17 % 2 = 1) ∧ ((17 ≥ 1) ∧ (52 ≥ 1)))) ∧ (((52 % 2 = 1 ∨ 52 % 2 = 0) ∧ (52 / 2 = 26)) ∧ ((52 % 2 = 0) ∧ ((52 ≥ 1) ∧ (26 ≥ 1))))) ∧ ((((26 % 2 = 1 ∨ 26 % 2 = 0) ∧ (26 / 2 = 13)) ∧ ((26 % 2 = 0) ∧ ((26 ≥ 1) ∧ (13 ≥ 1)))) ∧ (((13 % 2 = 1 ∨ 13 % 2 = 0) ∧ (3 * 13 + 1 = 40)) ∧ ((13 % 2 = 1) ∧ ((13 ≥ 1) ∧ (40 ≥ 1))))))) ∧ ((((((40 % 2 = 1 ∨ 40 % 2 = 0) ∧ (40 / 2 = 20)) ∧ ((40 % 2 = 0) ∧ ((40 ≥ 1) ∧ (20 ≥ 1)))) ∧ (((20 % 2 = 1 ∨ 20 % 2 = 0) ∧ (20 / 2 = 10)) ∧ ((20 % 2 = 0) ∧ ((20 ≥ 1) ∧ (10 ≥ 1))))) ∧ ((((10 % 2 = 1 ∨ 10 % 2 = 0) ∧ (10 / 2 = 5)) ∧ ((10 % 2 = 0) ∧ ((10 ≥ 1) ∧ (5 ≥ 1)))) ∧ (((5 % 2 = 1 ∨ 5 % 2 = 0) ∧ (3 * 5 + 1 = 16)) ∧ ((5 % 2 = 1) ∧ ((5 ≥ 1) ∧ (16 ≥ 1)))))) ∧ (((((16 % 2 = 1 ∨ 16 % 2 = 0) ∧ (16 / 2 = 8)) ∧ ((16 % 2 = 0) ∧ ((16 ≥ 1) ∧ (8 ≥ 1)))) ∧ (((8 % 2 = 1 ∨ 8 % 2 = 0) ∧ (8 / 2 = 4)) ∧ ((8 % 2 = 0) ∧ ((8 ≥ 1) ∧ (4 ≥ 1))))) ∧ ((((4 % 2 = 1 ∨ 4 % 2 = 0) ∧ (4 / 2 = 2)) ∧ ((4 % 2 = 0) ∧ ((4 ≥ 1) ∧ (2 ≥ 1)))) ∧ (((2 % 2 = 1 ∨ 2 % 2 = 0) ∧ ((2 / 2 = 1) ∧ (2 % 2 = 0))) ∧ ((2 ≥ 1) ∧ ((1 ≥ 1) ∧ (1 = 1))))))))

theorem jsp941 : R0 := by

  have h_0 : (7 % 2 = 1 ∨ 7 % 2 = 0) := by decide
  have h_1 : (3 * 7 + 1 = 22) := by decide
  have h_2 : (7 % 2 = 1) := by decide
  have h_3 : (7 ≥ 1) := by decide
  have h_4 : (22 ≥ 1) := by decide
  have h_5 : (22 % 2 = 1 ∨ 22 % 2 = 0) := by decide
  have h_6 : (22 / 2 = 11) := by decide
  have h_7 : (22 % 2 = 0) := by decide
  have h_8 : (22 ≥ 1) := by decide
  have h_9 : (11 ≥ 1) := by decide
  have h_10 : (11 % 2 = 1 ∨ 11 % 2 = 0) := by decide
  have h_11 : (3 * 11 + 1 = 34) := by decide
  have h_12 : (11 % 2 = 1) := by decide
  have h_13 : (11 ≥ 1) := by decide
  have h_14 : (34 ≥ 1) := by decide
  have h_15 : (34 % 2 = 1 ∨ 34 % 2 = 0) := by decide
  have h_16 : (34 / 2 = 17) := by decide
  have h_17 : (34 % 2 = 0) := by decide
  have h_18 : (34 ≥ 1) := by decide
  have h_19 : (17 ≥ 1) := by decide
  have h_20 : (17 % 2 = 1 ∨ 17 % 2 = 0) := by decide
  have h_21 : (3 * 17 + 1 = 52) := by decide
  have h_22 : (17 % 2 = 1) := by decide
  have h_23 : (17 ≥ 1) := by decide
  have h_24 : (52 ≥ 1) := by decide
  have h_25 : (52 % 2 = 1 ∨ 52 % 2 = 0) := by decide
  have h_26 : (52 / 2 = 26) := by decide
  have h_27 : (52 % 2 = 0) := by decide
  have h_28 : (52 ≥ 1) := by decide
  have h_29 : (26 ≥ 1) := by decide
  have h_30 : (26 % 2 = 1 ∨ 26 % 2 = 0) := by decide
  have h_31 : (26 / 2 = 13) := by decide
  have h_32 : (26 % 2 = 0) := by decide
  have h_33 : (26 ≥ 1) := by decide
  have h_34 : (13 ≥ 1) := by decide
  have h_35 : (13 % 2 = 1 ∨ 13 % 2 = 0) := by decide
  have h_36 : (3 * 13 + 1 = 40) := by decide
  have h_37 : (13 % 2 = 1) := by decide
  have h_38 : (13 ≥ 1) := by decide
  have h_39 : (40 ≥ 1) := by decide
  have h_40 : (40 % 2 = 1 ∨ 40 % 2 = 0) := by decide
  have h_41 : (40 / 2 = 20) := by decide
  have h_42 : (40 % 2 = 0) := by decide
  have h_43 : (40 ≥ 1) := by decide
  have h_44 : (20 ≥ 1) := by decide
  have h_45 : (20 % 2 = 1 ∨ 20 % 2 = 0) := by decide
  have h_46 : (20 / 2 = 10) := by decide
  have h_47 : (20 % 2 = 0) := by decide
  have h_48 : (20 ≥ 1) := by decide
  have h_49 : (10 ≥ 1) := by decide
  have h_50 : (10 % 2 = 1 ∨ 10 % 2 = 0) := by decide
  have h_51 : (10 / 2 = 5) := by decide
  have h_52 : (10 % 2 = 0) := by decide
  have h_53 : (10 ≥ 1) := by decide
  have h_54 : (5 ≥ 1) := by decide
  have h_55 : (5 % 2 = 1 ∨ 5 % 2 = 0) := by decide
  have h_56 : (3 * 5 + 1 = 16) := by decide
  have h_57 : (5 % 2 = 1) := by decide
  have h_58 : (5 ≥ 1) := by decide
  have h_59 : (16 ≥ 1) := by decide
  have h_60 : (16 % 2 = 1 ∨ 16 % 2 = 0) := by decide
  have h_61 : (16 / 2 = 8) := by decide
  have h_62 : (16 % 2 = 0) := by decide
  have h_63 : (16 ≥ 1) := by decide
  have h_64 : (8 ≥ 1) := by decide
  have h_65 : (8 % 2 = 1 ∨ 8 % 2 = 0) := by decide
  have h_66 : (8 / 2 = 4) := by decide
  have h_67 : (8 % 2 = 0) := by decide
  have h_68 : (8 ≥ 1) := by decide
  have h_69 : (4 ≥ 1) := by decide
  have h_70 : (4 % 2 = 1 ∨ 4 % 2 = 0) := by decide
  have h_71 : (4 / 2 = 2) := by decide
  have h_72 : (4 % 2 = 0) := by decide
  have h_73 : (4 ≥ 1) := by decide
  have h_74 : (2 ≥ 1) := by decide
  have h_75 : (2 % 2 = 1 ∨ 2 % 2 = 0) := by decide
  have h_76 : (2 / 2 = 1) := by decide
  have h_77 : (2 % 2 = 0) := by decide
  have h_78 : (2 ≥ 1) := by decide
  have h_79 : (1 ≥ 1) := by decide
  have h_80 : (1 = 1) := by decide
  exact ⟨⟨⟨⟨⟨⟨h_0, h_1⟩, ⟨h_2, ⟨h_3, h_4⟩⟩⟩, ⟨⟨h_5, h_6⟩, ⟨h_7, ⟨h_8, h_9⟩⟩⟩⟩, ⟨⟨⟨h_10, h_11⟩, ⟨h_12, ⟨h_13, h_14⟩⟩⟩, ⟨⟨h_15, h_16⟩, ⟨h_17, ⟨h_18, h_19⟩⟩⟩⟩⟩, ⟨⟨⟨⟨h_20, h_21⟩, ⟨h_22, ⟨h_23, h_24⟩⟩⟩, ⟨⟨h_25, h_26⟩, ⟨h_27, ⟨h_28, h_29⟩⟩⟩⟩, ⟨⟨⟨h_30, h_31⟩, ⟨h_32, ⟨h_33, h_34⟩⟩⟩, ⟨⟨h_35, h_36⟩, ⟨h_37, ⟨h_38, h_39⟩⟩⟩⟩⟩⟩, ⟨⟨⟨⟨⟨h_40, h_41⟩, ⟨h_42, ⟨h_43, h_44⟩⟩⟩, ⟨⟨h_45, h_46⟩, ⟨h_47, ⟨h_48, h_49⟩⟩⟩⟩, ⟨⟨⟨h_50, h_51⟩, ⟨h_52, ⟨h_53, h_54⟩⟩⟩, ⟨⟨h_55, h_56⟩, ⟨h_57, ⟨h_58, h_59⟩⟩⟩⟩⟩, ⟨⟨⟨⟨h_60, h_61⟩, ⟨h_62, ⟨h_63, h_64⟩⟩⟩, ⟨⟨h_65, h_66⟩, ⟨h_67, ⟨h_68, h_69⟩⟩⟩⟩, ⟨⟨⟨h_70, h_71⟩, ⟨h_72, ⟨h_73, h_74⟩⟩⟩, ⟨⟨h_75, ⟨h_76, h_77⟩⟩, ⟨h_78, ⟨h_79, h_80⟩⟩⟩⟩⟩⟩⟩
