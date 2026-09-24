-- =====================================================================
-- JSP-001017 — 孙宇晨奖 (The Justin Sun Prize) 形式化提交
--
-- 题目：In the lattice graph of coprime coordinate pairs, is there an
--       infinite path avoiding every point with both coordinates prime?
--       （在互素坐标对的格点图中，是否存在一条无限路径，避开所有
--         两个坐标均为素数的点？）
--
-- 答案：是。取路径 f(k) = (k+1, 1)：
--   · gcd(k+1, 1) = 1，故每步都在互素坐标对图中；
--   · 第二坐标恒为 1（非素数），故永不落在“两坐标均素数”的点上；
--   · 相邻点 (k+1,1) → (k+2,1) 相差一单位，构成无限路径。
--
-- 环境：Lean 4.28.0-pre (wasm32)，仅依赖核心库 + Std，无 Mathlib。
-- 核验：node run-lean.js jsp1017.lean
-- =====================================================================

set_option maxRecDepth 1000000

def Prime (p : Nat) : Prop := p ≥ 2 ∧ ∀ m : Nat, m ∣ p → m = 1 ∨ m = p

/-- 格点相邻：曼哈顿距离为 1。-/
def Adj (u v : Nat × Nat) : Prop :=
  (u.1 + 1 = v.1 ∧ u.2 = v.2) ∨
  (u.1 = v.1 ∧ u.2 + 1 = v.2) ∨
  (u.1 = v.1 + 1 ∧ u.2 = v.2) ∨
  (u.1 = v.1 ∧ u.2 = v.2 + 1)

/-- 主定理：存在无限路径 (k+1, 1)_{k≥0}，路径上每点的坐标互素、
    不出现“两坐标均素数”的点、且相邻两点曼哈顿距离为 1。 -/
theorem jsp1017 :
    ∃ f : Nat → Nat × Nat,
      (∀ k : Nat, Nat.gcd (f k).1 (f k).2 = 1) ∧
      (∀ k : Nat, ¬ (Prime (f k).1 ∧ Prime (f k).2)) ∧
      (∀ k : Nat, Adj (f k) (f (k + 1))) := by
  refine ⟨fun k => (k + 1, 1), ?_⟩
  constructor
  · intro k
    change Nat.gcd (k + 1) 1 = 1
    have hd : Nat.gcd (k + 1) 1 ∣ 1 := Nat.gcd_dvd_right (k + 1) 1
    have hg : 0 < Nat.gcd (k + 1) 1 := Nat.gcd_pos_of_pos_right (k + 1) (by decide : 0 < 1)
    have hle : Nat.gcd (k + 1) 1 ≤ 1 := Nat.le_of_dvd (by decide : 0 < 1) hd
    omega
  · constructor
    · intro k hb
      change Prime (k + 1) ∧ Prime 1 at hb
      exfalso
      have hp1 : 1 ≥ 2 := hb.2.1
      omega
    · intro k
      refine Or.inl ⟨?_, ?_⟩
      · rfl
      · rfl
